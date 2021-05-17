import dataclasses

from equivalence import db, checker

import pytest


@dataclasses.dataclass
class Case:
    name: str
    query1: str
    query2: str
    are_equivalent: bool

    def __str__(self):
        return f"test_{self.name}"


CALCITE_TEST_CASES = [
    Case(
        "testReduceConstantsRequiresExecutor",
        "SELECT * FROM (VALUES  (1, 2)) AS t WHERE 1 + 2 > 3 + NULL",
        "SELECT * FROM (VALUES  (1, 2)) AS t1 WHERE 1 + 2 > 3 + NULL",
        True
    ),
    Case(
        "testMergeJoinFilter",
        "SELECT * FROM (SELECT DEPT.DEPTNO, EMP.ENAME FROM EMP AS EMP INNER JOIN DEPT AS DEPT ON EMP.DEPTNO = DEPT.DEPTNO AND DEPT.DEPTNO = 10) AS t WHERE t.DEPTNO = 10",
        "SELECT t1.DEPTNO, EMP0.ENAME FROM EMP AS EMP0 INNER JOIN (SELECT * FROM DEPT AS DEPT0 WHERE DEPT0.DEPTNO = 10) AS t1 ON EMP0.DEPTNO = t1.DEPTNO",
        True
    ),
    Case(
        "testTransitiveInferenceLeftOuterJoin",
        "SELECT 1 FROM (SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO > 7) AS t LEFT JOIN EMP AS EMP0 ON t.DEPTNO = EMP0.DEPTNO WHERE EMP0.DEPTNO > 9",
        "SELECT 1 FROM (SELECT * FROM EMP AS EMP1 WHERE EMP1.DEPTNO > 7) AS t2 LEFT JOIN (SELECT * FROM EMP AS EMP2 WHERE EMP2.DEPTNO > 7) AS t3 ON t2.DEPTNO = t3.DEPTNO WHERE t3.DEPTNO > 9",
        True
    ),
    Case(
        "testTransitiveInferenceProject",
        "SELECT 1 FROM (SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO > 7) AS t INNER JOIN EMP AS EMP0 ON t.DEPTNO = EMP0.DEPTNO",
        "SELECT 1 FROM (SELECT * FROM EMP AS EMP1 WHERE EMP1.DEPTNO > 7) AS t1 INNER JOIN (SELECT * FROM EMP AS EMP2 WHERE EMP2.DEPTNO > 7) AS t2 ON t1.DEPTNO = t2.DEPTNO",
        True
    ),
    Case(
        "testRemoveSemiJoinWithFilter",
        "SELECT EMP.ENAME FROM EMP AS EMP, DEPT AS DEPT WHERE EMP.DEPTNO = DEPT.DEPTNO AND EMP.ENAME = 'foo'",
        "SELECT t1.ENAME FROM (SELECT * FROM EMP AS EMP0 WHERE EMP0.ENAME = 'foo') AS t1 INNER JOIN DEPT AS DEPT0 ON t1.DEPTNO = DEPT0.DEPTNO",
        True
    ),
    Case(
        "testMergeMinusRightDeep",
        "SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO = 10 EXCEPT SELECT * FROM (SELECT * FROM EMP AS EMP0 WHERE EMP0.DEPTNO = 20 EXCEPT SELECT * FROM EMP AS EMP1 WHERE EMP1.DEPTNO = 30) AS t2",
        "SELECT * FROM EMP AS EMP2 WHERE EMP2.DEPTNO = 10 EXCEPT SELECT * FROM (SELECT * FROM EMP AS EMP3 WHERE EMP3.DEPTNO = 20 EXCEPT SELECT * FROM EMP AS EMP4 WHERE EMP4.DEPTNO = 30) AS t7",
        True
    ),
    Case(
        "testTransitiveInferencePullUpThruAlias",
        "SELECT 1 FROM (SELECT EMP.COMM AS DEPTNO FROM EMP AS EMP WHERE EMP.COMM > 7) AS t0 INNER JOIN EMP AS EMP0 ON t0.DEPTNO = EMP0.DEPTNO",
        "SELECT 1 FROM (SELECT EMP1.COMM AS DEPTNO FROM EMP AS EMP1 WHERE EMP1.COMM > 7) AS t3 INNER JOIN (SELECT * FROM EMP AS EMP2 WHERE EMP2.DEPTNO > 7) AS t4 ON t3.DEPTNO = t4.DEPTNO",
        True
    ),
    Case(
        "testReduceConstants2",
        "SELECT CAST(CASE WHEN NULL IS NULL THEN 2 IS NULL WHEN 2 IS NULL THEN NULL IS NULL ELSE NULL = 2 END AS BOOLEAN) FROM (VALUES  (0)) AS t",
        "SELECT FALSE FROM (VALUES  (0)) AS t2",
        True
    ),
    Case(
        "testTransitiveInferenceComplexPredicate",
        "SELECT 1 FROM (SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO > 7 AND EMP.COMM = EMP.DEPTNO AND EMP.COMM + EMP.DEPTNO > EMP.COMM / 2) AS t INNER JOIN (SELECT * FROM EMP AS EMP0 WHERE EMP0.SAL = EMP0.DEPTNO) AS t0 ON t.DEPTNO = t0.DEPTNO",
        "SELECT 1 FROM (SELECT * FROM EMP AS EMP1 WHERE EMP1.DEPTNO > 7 AND EMP1.COMM = EMP1.DEPTNO AND EMP1.COMM + EMP1.DEPTNO > EMP1.COMM / 2) AS t2 INNER JOIN (SELECT * FROM (SELECT * FROM EMP AS EMP2 WHERE EMP2.SAL = EMP2.DEPTNO) AS t3 WHERE t3.DEPTNO > 7) AS t4 ON t2.DEPTNO = t4.DEPTNO",
        True
    ),
    Case(
        "testMergeUnionMixed",
        "SELECT * FROM (SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO = 10 UNION SELECT * FROM EMP AS EMP0 WHERE EMP0.DEPTNO = 20) AS t1 UNION ALL SELECT * FROM EMP AS EMP1 WHERE EMP1.DEPTNO = 30",
        "SELECT * FROM (SELECT * FROM EMP AS EMP2 WHERE EMP2.DEPTNO = 10 UNION SELECT * FROM EMP AS EMP3 WHERE EMP3.DEPTNO = 20) AS t6 UNION ALL SELECT * FROM EMP AS EMP4 WHERE EMP4.DEPTNO = 30",
        True
    ),
    Case(
        "testRightOuterJoinSimplificationToInner",
        "SELECT 1 FROM DEPT AS DEPT RIGHT JOIN EMP AS EMP ON DEPT.DEPTNO = EMP.DEPTNO WHERE DEPT.NAME = 'Charlie'",
        "SELECT 1 FROM (SELECT * FROM DEPT AS DEPT0 WHERE DEPT0.NAME = 'Charlie') AS t1 INNER JOIN EMP AS EMP0 ON t1.DEPTNO = EMP0.DEPTNO",
        True
    ),
    Case(
        "testPullConstantThroughUnion2",
        "SELECT 2, EMP.DEPTNO, EMP.JOB FROM EMP AS EMP UNION ALL SELECT 1, EMP0.DEPTNO, EMP0.JOB FROM EMP AS EMP0",
        "SELECT 2, EMP1.DEPTNO, EMP1.JOB FROM EMP AS EMP1 UNION ALL SELECT 1, EMP2.DEPTNO, EMP2.JOB FROM EMP AS EMP2",
        True
    ),
    Case(
        "testSemiJoinRuleLeft",
        "SELECT DEPT.NAME FROM DEPT AS DEPT LEFT JOIN (SELECT EMP.DEPTNO FROM EMP AS EMP WHERE EMP.SAL > 100 GROUP BY EMP.DEPTNO) AS t1 ON DEPT.DEPTNO = t1.DEPTNO",
        "SELECT DEPT0.NAME FROM DEPT AS DEPT0",
        True
    ),
    Case(
        "testRemoveSemiJoinRight",
        "SELECT EMP.ENAME FROM EMP AS EMP, DEPT AS DEPT, EMP AS EMP0 WHERE EMP.DEPTNO = DEPT.DEPTNO AND DEPT.DEPTNO = EMP0.DEPTNO",
        "SELECT EMP1.ENAME FROM EMP AS EMP1 INNER JOIN DEPT AS DEPT0 ON EMP1.DEPTNO = DEPT0.DEPTNO INNER JOIN EMP AS EMP2 ON DEPT0.DEPTNO = EMP2.DEPTNO",
        True
    ),
    Case(
        "testExtractJoinFilterRule",
        "SELECT 1 FROM EMP AS EMP INNER JOIN DEPT AS DEPT ON EMP.DEPTNO = DEPT.DEPTNO",
        "SELECT 1 FROM EMP AS EMP0, DEPT AS DEPT0 WHERE EMP0.DEPTNO = DEPT0.DEPTNO",
        True
    ),
    Case(
        "testPushAvgThroughUnion",
        "SELECT t.ENAME, AVG(t.EMPNO) FROM (SELECT * FROM EMP AS EMP UNION ALL SELECT * FROM EMP AS EMP0) AS t GROUP BY t.ENAME",
        "SELECT t4.ENAME, AVG(t4.EMPNO) FROM (SELECT EMP1.ENAME, EMP1.EMPNO FROM EMP AS EMP1 UNION ALL SELECT EMP2.ENAME, EMP2.EMPNO FROM EMP AS EMP2) AS t4 GROUP BY t4.ENAME",
        True
    ),
    Case(
        "testReduceConstantsIsNotNull",
        "SELECT EMP.EMPNO FROM EMP AS EMP WHERE EMP.EMPNO = 10 AND EMP.EMPNO IS NOT NULL",
        "SELECT EMP0.EMPNO FROM EMP AS EMP0 WHERE EMP0.EMPNO = 10",
        True
    ),
    Case(
        "testAggregateConstantKeyRule2",
        "SELECT COUNT(*) AS C FROM EMP AS EMP WHERE EMP.DEPTNO = 10 GROUP BY EMP.DEPTNO",
        "SELECT COUNT(*) AS C FROM EMP AS EMP0 WHERE EMP0.DEPTNO = 10 GROUP BY EMP0.DEPTNO",
        True
    ),
    Case(
        "testReduceCastAndConsts",
        "SELECT * FROM EMP AS EMP WHERE CAST(EMP.EMPNO + 10 / 2 AS INTEGER) = 13",
        "SELECT * FROM EMP AS EMP0 WHERE EMP0.EMPNO + 5 = 13",
        True
    ),
    Case(
        "testTransitiveInferenceConstantEquiPredicate",
        "SELECT 1 FROM EMP AS EMP INNER JOIN EMP AS EMP0 ON EMP.DEPTNO = EMP0.DEPTNO",
        "SELECT 1 FROM EMP AS EMP1 INNER JOIN EMP AS EMP2 ON EMP1.DEPTNO = EMP2.DEPTNO",
        True
    ),
    Case(
        "testTransitiveInferenceRightOuterJoin",
        "SELECT 1 FROM EMP AS EMP RIGHT JOIN (SELECT * FROM EMP AS EMP0 WHERE EMP0.DEPTNO > 9) AS t ON EMP.DEPTNO = t.DEPTNO WHERE EMP.DEPTNO > 7",
        "SELECT 1 FROM (SELECT * FROM EMP AS EMP1 WHERE EMP1.DEPTNO > 9) AS t2 RIGHT JOIN (SELECT * FROM EMP AS EMP2 WHERE EMP2.DEPTNO > 9) AS t3 ON t2.DEPTNO = t3.DEPTNO WHERE t2.DEPTNO > 7",
        True
    ),
    Case(
        "testTransitiveInferenceJoin3way",
        "SELECT 1 FROM (SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO > 7) AS t INNER JOIN EMP AS EMP0 ON t.DEPTNO = EMP0.DEPTNO INNER JOIN EMP AS EMP1 ON EMP0.DEPTNO = EMP1.DEPTNO",
        "SELECT 1 FROM (SELECT * FROM EMP AS EMP2 WHERE EMP2.DEPTNO > 7) AS t1 INNER JOIN (SELECT * FROM EMP AS EMP3 WHERE EMP3.DEPTNO > 7) AS t2 ON t1.DEPTNO = t2.DEPTNO INNER JOIN (SELECT * FROM EMP AS EMP4 WHERE EMP4.DEPTNO > 7) AS t3 ON t2.DEPTNO = t3.DEPTNO",
        True
    ),
    Case(
        "testMergeSetOpMixed",
        "SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO = 10 UNION SELECT * FROM (SELECT * FROM EMP AS EMP0 WHERE EMP0.DEPTNO = 20 INTERSECT SELECT * FROM EMP AS EMP1 WHERE EMP1.DEPTNO = 30) AS t2",
        "SELECT * FROM EMP AS EMP2 WHERE EMP2.DEPTNO = 10 UNION SELECT * FROM (SELECT * FROM EMP AS EMP3 WHERE EMP3.DEPTNO = 20 INTERSECT SELECT * FROM EMP AS EMP4 WHERE EMP4.DEPTNO = 30) AS t7",
        True
    ),
    Case(
        "testPullNull",
        "SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO = 7 AND EMP.EMPNO = 10 AND EMP.MGR IS NULL AND EMP.EMPNO = 10",
        "SELECT 10 AS EMPNO, EMP0.ENAME, EMP0.JOB, NULL AS MGR, EMP0.HIREDATE, EMP0.SAL, EMP0.COMM, 7 AS DEPTNO, EMP0.SLACKER FROM EMP AS EMP0 WHERE EMP0.DEPTNO = 7 AND EMP0.MGR IS NULL AND EMP0.EMPNO = 10",
        True
    ),
    Case(
        "testRemoveSemiJoin",
        "SELECT EMP.ENAME FROM EMP AS EMP, DEPT AS DEPT WHERE EMP.DEPTNO = DEPT.DEPTNO",
        "SELECT EMP0.ENAME FROM EMP AS EMP0 INNER JOIN DEPT AS DEPT0 ON EMP0.DEPTNO = DEPT0.DEPTNO",
        True
    ),
    Case(
        "testPushFilterWithRankExpr",
        "SELECT * FROM (SELECT EMP.ENAME, (RANK() OVER (PARTITION BY EMP.DEPTNO ORDER BY EMP.SAL RANGE BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW)) + 1 AS R FROM EMP AS EMP) AS t WHERE t.R < 2",
        "SELECT * FROM (SELECT EMP0.ENAME, (RANK() OVER (PARTITION BY EMP0.DEPTNO ORDER BY EMP0.SAL RANGE BETWEEN UNBOUNDED PRECEDING AND CURRENT ROW)) + 1 AS R FROM EMP AS EMP0) AS t1 WHERE t1.R < 2",
        True
    ),
    Case(
        "testLeftOuterJoinSimplificationToInner",
        "SELECT 1 FROM DEPT AS DEPT LEFT JOIN EMP AS EMP ON DEPT.DEPTNO = EMP.DEPTNO WHERE EMP.SAL > 100",
        "SELECT 1 FROM DEPT AS DEPT0 INNER JOIN (SELECT * FROM EMP AS EMP0 WHERE EMP0.SAL > 100) AS t1 ON DEPT0.DEPTNO = t1.DEPTNO",
        True
    ),
    Case(
        "testPullConstantIntoProject",
        "SELECT EMP.DEPTNO, EMP.DEPTNO + 1, EMP.EMPNO + EMP.DEPTNO FROM EMP AS EMP WHERE EMP.DEPTNO = 10",
        "SELECT 10 AS DEPTNO, 11, EMP0.EMPNO + 10 FROM EMP AS EMP0 WHERE EMP0.DEPTNO = 10",
        True
    ),
    Case(
        "testPushAvgGroupingSetsThroughUnion",
        "SELECT t.DEPTNO, t.JOB, AVG(t.EMPNO) FROM (SELECT * FROM EMP AS EMP UNION ALL SELECT * FROM EMP AS EMP0) AS t GROUP BY t.DEPTNO, t.JOB",
        "SELECT t4.DEPTNO, t4.JOB, AVG(t4.EMPNO) FROM (SELECT EMP1.DEPTNO, EMP1.JOB, EMP1.EMPNO FROM EMP AS EMP1 UNION ALL SELECT EMP2.DEPTNO, EMP2.JOB, EMP2.EMPNO FROM EMP AS EMP2) AS t4 GROUP BY t4.DEPTNO, t4.JOB",
        True
    ),
    Case(
        "testFullOuterJoinSimplificationToInner",
        "SELECT 1 FROM DEPT AS DEPT FULL JOIN EMP AS EMP ON DEPT.DEPTNO = EMP.DEPTNO WHERE DEPT.NAME = 'Charlie' AND EMP.SAL > 100",
        "SELECT 1 FROM (SELECT * FROM DEPT AS DEPT0 WHERE DEPT0.NAME = 'Charlie') AS t1 INNER JOIN (SELECT * FROM EMP AS EMP0 WHERE EMP0.SAL > 100) AS t2 ON t1.DEPTNO = t2.DEPTNO",
        True
    ),
    Case(
        "testRemoveSemiJoinRightWithFilter",
        "SELECT EMP.ENAME FROM EMP AS EMP, DEPT AS DEPT, EMP AS EMP0 WHERE EMP.DEPTNO = DEPT.DEPTNO AND DEPT.DEPTNO = EMP0.DEPTNO AND DEPT.NAME = 'foo'",
        "SELECT EMP1.ENAME FROM EMP AS EMP1 INNER JOIN (SELECT * FROM DEPT AS DEPT0 WHERE DEPT0.NAME = 'foo') AS t1 ON EMP1.DEPTNO = t1.DEPTNO INNER JOIN EMP AS EMP2 ON t1.DEPTNO = EMP2.DEPTNO",
        True
    ),
    Case(
        "testTransitiveInferenceJoin",
        "SELECT 1 FROM EMP AS EMP INNER JOIN (SELECT * FROM EMP AS EMP0 WHERE EMP0.DEPTNO > 7) AS t ON EMP.DEPTNO = t.DEPTNO",
        "SELECT 1 FROM (SELECT * FROM EMP AS EMP1 WHERE EMP1.DEPTNO > 7) AS t1 INNER JOIN (SELECT * FROM EMP AS EMP2 WHERE EMP2.DEPTNO > 7) AS t2 ON t1.DEPTNO = t2.DEPTNO",
        True
    ),
    Case(
        "testMergeUnionMixed2",
        "SELECT * FROM (SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO = 10 UNION ALL SELECT * FROM EMP AS EMP0 WHERE EMP0.DEPTNO = 20) AS t1 UNION SELECT * FROM EMP AS EMP1 WHERE EMP1.DEPTNO = 30",
        "SELECT * FROM EMP AS EMP2 WHERE EMP2.DEPTNO = 10 UNION SELECT * FROM EMP AS EMP3 WHERE EMP3.DEPTNO = 20 UNION SELECT * FROM EMP AS EMP4 WHERE EMP4.DEPTNO = 30",
        True
    ),
    Case(
        "testPushProjectPastSetOp",
        "SELECT t.SAL FROM (SELECT * FROM EMP AS EMP UNION ALL SELECT * FROM EMP AS EMP0) AS t",
        "SELECT EMP1.SAL FROM EMP AS EMP1 UNION ALL SELECT EMP2.SAL FROM EMP AS EMP2",
        True
    ),
    Case(
        "testAggregateConstantKeyRule",
        "SELECT COUNT(*) AS C FROM EMP AS EMP WHERE EMP.DEPTNO = 10 GROUP BY EMP.DEPTNO, EMP.SAL",
        "SELECT COUNT(*) AS C FROM EMP AS EMP0 WHERE EMP0.DEPTNO = 10 GROUP BY EMP0.SAL",
        True
    ),
    Case(
        "testMergeUnionDistinct",
        "SELECT * FROM (SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO = 10 UNION SELECT * FROM EMP AS EMP0 WHERE EMP0.DEPTNO = 20) AS t1 UNION SELECT * FROM EMP AS EMP1 WHERE EMP1.DEPTNO = 30",
        "SELECT * FROM EMP AS EMP2 WHERE EMP2.DEPTNO = 10 UNION SELECT * FROM EMP AS EMP3 WHERE EMP3.DEPTNO = 20 UNION SELECT * FROM EMP AS EMP4 WHERE EMP4.DEPTNO = 30",
        True
    ),
    Case(
        "testUnionMergeRule",
        "SELECT * FROM (SELECT DEPT.NAME, DEPT.DEPTNO FROM DEPT AS DEPT UNION ALL SELECT t4.NAME, t4.DEPTNO FROM (SELECT DEPT0.NAME, DEPT0.DEPTNO, COUNT(*) FROM DEPT AS DEPT0 GROUP BY DEPT0.NAME, DEPT0.DEPTNO UNION ALL SELECT DEPT1.NAME, DEPT1.DEPTNO, COUNT(*) FROM DEPT AS DEPT1 GROUP BY DEPT1.NAME, DEPT1.DEPTNO) AS t4) AS t6 UNION ALL SELECT DEPT2.NAME, DEPT2.DEPTNO FROM DEPT AS DEPT2",
        "SELECT DEPT3.NAME, DEPT3.DEPTNO FROM DEPT AS DEPT3 UNION ALL SELECT DEPT4.NAME, DEPT4.DEPTNO FROM DEPT AS DEPT4 GROUP BY DEPT4.NAME, DEPT4.DEPTNO UNION ALL SELECT DEPT5.NAME, DEPT5.DEPTNO FROM DEPT AS DEPT5 GROUP BY DEPT5.NAME, DEPT5.DEPTNO UNION ALL SELECT DEPT6.NAME, DEPT6.DEPTNO FROM DEPT AS DEPT6",
        True
    ),
    Case(
        "testUnionToDistinctRule",
        "SELECT * FROM DEPT AS DEPT UNION SELECT * FROM DEPT AS DEPT0",
        "SELECT t0.DEPTNO, t0.NAME FROM (SELECT * FROM DEPT AS DEPT1 UNION ALL SELECT * FROM DEPT AS DEPT2) AS t0 GROUP BY t0.DEPTNO, t0.NAME",
        True
    ),
    Case(
        "testPushAggregateThroughJoin3",
        "SELECT t.EMPNO, DEPT.DEPTNO AS DEPTNO0 FROM (SELECT * FROM EMP AS EMP WHERE EMP.EMPNO = 10) AS t INNER JOIN DEPT AS DEPT ON t.EMPNO < DEPT.DEPTNO GROUP BY t.EMPNO, DEPT.DEPTNO",
        "SELECT t1.EMPNO, DEPT0.DEPTNO AS DEPTNO0 FROM (SELECT * FROM EMP AS EMP0 WHERE EMP0.EMPNO = 10) AS t1 INNER JOIN DEPT AS DEPT0 ON t1.EMPNO < DEPT0.DEPTNO GROUP BY t1.EMPNO, DEPT0.DEPTNO",
        True
    ),
    Case(
        "testTransitiveInferencePreventProjectPullUp",
        "SELECT 1 FROM (SELECT EMP.COMM AS DEPTNO FROM EMP AS EMP WHERE EMP.DEPTNO > 7) AS t0 INNER JOIN EMP AS EMP0 ON t0.DEPTNO = EMP0.DEPTNO",
        "SELECT 1 FROM (SELECT EMP1.COMM AS DEPTNO FROM EMP AS EMP1 WHERE EMP1.DEPTNO > 7) AS t3 INNER JOIN EMP AS EMP2 ON t3.DEPTNO = EMP2.DEPTNO",
        True
    ),
    Case(
        "testReduceConstantsProjectNullable",
        "SELECT EMP.MGR FROM EMP AS EMP WHERE EMP.MGR = 10",
        "SELECT CAST(10 AS INTEGER) AS MGR FROM EMP AS EMP0 WHERE EMP0.MGR = 10",
        True
    ),
    Case(
        "testPushFilterPastAggThree",
        "SELECT EMP.DEPTNO FROM EMP AS EMP GROUP BY EMP.DEPTNO HAVING COUNT(*) > 1",
        "SELECT EMP0.DEPTNO FROM EMP AS EMP0 GROUP BY EMP0.DEPTNO HAVING COUNT(*) > 1",
        True
    ),
    Case(
        "testMergeUnionAll",
        "SELECT * FROM (SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO = 10 UNION ALL SELECT * FROM EMP AS EMP0 WHERE EMP0.DEPTNO = 20) AS t1 UNION ALL SELECT * FROM EMP AS EMP1 WHERE EMP1.DEPTNO = 30",
        "SELECT * FROM EMP AS EMP2 WHERE EMP2.DEPTNO = 10 UNION ALL SELECT * FROM EMP AS EMP3 WHERE EMP3.DEPTNO = 20 UNION ALL SELECT * FROM EMP AS EMP4 WHERE EMP4.DEPTNO = 30",
        True
    ),
    Case(
        "testAggregateProjectMerge",
        "SELECT * FROM (SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO = 10 UNION ALL SELECT * FROM EMP AS EMP0 WHERE EMP0.DEPTNO = 20) AS t1 UNION ALL SELECT * FROM EMP AS EMP1 WHERE EMP1.DEPTNO = 30",
        "SELECT * FROM EMP AS EMP2 WHERE EMP2.DEPTNO = 10 UNION ALL SELECT * FROM EMP AS EMP3 WHERE EMP3.DEPTNO = 20 UNION ALL SELECT * FROM EMP AS EMP4 WHERE EMP4.DEPTNO = 30",
        True
    ),
    Case(
        "testReduceConstantsNull",
        "SELECT * FROM (SELECT * FROM (SELECT NULL AS N FROM EMP AS EMP) AS t WHERE t.N IS NULL AND t.N IS NULL) AS t0 WHERE t0.N IS NULL",
        "SELECT NULL AS N FROM EMP AS EMP0",
        True
    ),
    Case(
        "testPushFilterPastAggWithGroupingSets1",
        "SELECT DEPT.DEPTNO, DEPT.NAME, COUNT(*) AS C FROM DEPT AS DEPT GROUP BY DEPT.DEPTNO, DEPT.NAME HAVING DEPT.NAME = 'Charlie'",
        "SELECT DEPT0.DEPTNO, DEPT0.NAME, COUNT(*) AS C FROM DEPT AS DEPT0 GROUP BY DEPT0.DEPTNO, DEPT0.NAME HAVING DEPT0.NAME = 'Charlie'",
        True
    ),
    Case(
        "testTransitiveInferenceNoPullUpExprs",
        "SELECT 1 FROM (SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO = 7 OR EMP.DEPTNO = 9 OR EMP.COMM > 10) AS t INNER JOIN EMP AS EMP0 ON t.DEPTNO = EMP0.DEPTNO",
        "SELECT 1 FROM (SELECT * FROM EMP AS EMP1 WHERE EMP1.DEPTNO = 7 OR EMP1.DEPTNO = 9 OR EMP1.COMM > 10) AS t1 INNER JOIN EMP AS EMP2 ON t1.DEPTNO = EMP2.DEPTNO",
        True
    ),
    Case(
        "testTransitiveInferenceConjunctInPullUp",
        "SELECT 1 FROM (SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO = 7 OR EMP.DEPTNO = 9 OR EMP.DEPTNO > 10) AS t INNER JOIN EMP AS EMP0 ON t.DEPTNO = EMP0.DEPTNO",
        "SELECT 1 FROM (SELECT * FROM EMP AS EMP1 WHERE EMP1.DEPTNO = 7 OR EMP1.DEPTNO = 9 OR EMP1.DEPTNO > 10) AS t1 INNER JOIN (SELECT * FROM EMP AS EMP2 WHERE EMP2.DEPTNO = 7 OR EMP2.DEPTNO = 9 OR EMP2.DEPTNO > 10) AS t2 ON t1.DEPTNO = t2.DEPTNO",
        True
    ),
    Case(
        "testPullConstantIntoFilter",
        "SELECT * FROM (SELECT * FROM EMP AS EMP WHERE EMP.DEPTNO = 10) AS t WHERE t.DEPTNO + 5 > t.EMPNO",
        "SELECT * FROM (SELECT * FROM EMP AS EMP0 WHERE EMP0.DEPTNO = 10) AS t1 WHERE 15 > t1.EMPNO",
        True
    ),
]


@pytest.mark.parametrize("test_case", CALCITE_TEST_CASES, ids=str)
def test_calcite(test_case):
    plan_generator = db.PlanGenerator(
        db.ConnectionParameters("postgres", "postgres", "demo")
    )

    c = checker.Checker(plan_generator)

    assert test_case.are_equivalent == c.check(test_case.query1, test_case.query2)
