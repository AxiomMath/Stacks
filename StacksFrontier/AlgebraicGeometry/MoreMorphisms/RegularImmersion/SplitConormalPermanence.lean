module

public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SplitConormalH1Regular
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SplitConormalKoszulRegular
public import
  StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularImmersion.SplitConormalQuasiRegular

/-!
# Regularity of an immersion descends along a split conormal sequence

Let `i : Z ⟶ Y` and `j : Y ⟶ X` be immersions with `j` locally of finite presentation whose
conormal sequence is exact and locally split. Then quasi-regularity and `H₁`-regularity of
`i ≫ j` descend to `i`, and `i` is Koszul-regular as soon as both `j` and `i ≫ j` are
([Stacks, Tag 068Z]).
-/
