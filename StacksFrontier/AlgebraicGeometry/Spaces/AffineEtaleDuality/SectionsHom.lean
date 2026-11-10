module

public import StacksFrontier.AlgebraicGeometry.Spaces.AffineEtaleDuality.ChainMap
public import StacksFrontier.AlgebraicGeometry.Duality.DerivedTilde.AffineExt.TildeSliceHom

/-!
# Sections of the internal Hom complex out of `ε^* P̃`

For a complex `P` of `A`-modules, a complex `J` of `𝒪_étale`-modules and an object `V` of the
small étale site of `Spec A`, the complex of sections over `V` of the internal Hom complex
`SheafHom^•(ε^* P̃, J)` is the Hom complex of `A`-modules `Hom^•_A(P, J(V))`, up to the universe
lift. This is the slice universal property of `ε^*T`
(`AlgebraicGeometry.AffineEtaleDuality.sliceHomEquivA`) applied degreewise to the local
description of the internal Hom complex (Stacks 0A8X).

## Main definitions

* `AlgebraicGeometry.AffineEtaleDuality.sliceHomAddEquiv`: the slice universal property, as an
  additive equivalence.
* `AlgebraicGeometry.AffineEtaleDuality.sectionsHomIso`: the isomorphism of complexes
  `Γ(V, SheafHom^•(ε^* P̃, J)) ≅ Hom^•_A(P, J(V))`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite CochainComplex.HomComplex

universe u

namespace AlgebraicGeometry.AffineEtaleDuality

variable {A : CommRingCat.{u}} {B : BigEtaleSite.{u}} {hX : B.Contains (Spec A)}

/-- The slice universal property of `ε^*T`, as an additive equivalence. -/
def sliceHomAddEquiv (M : ModuleCat.{u} A) (H : Mod A B hX) (V : Site A B hX) :
    (((epsT A B hX).obj M).over V ⟶ H.over V) ≃+ (M ⟶ (secA A B hX V).obj H) where
  __ := sliceHomEquivA A B hX M H V
  map_add' φ ψ := by
    ext m
    exact (sliceHomEquivA_apply A B hX M H V (φ + ψ) m).trans
      (congrArg₂ (· + ·) (sliceHomEquivA_apply A B hX M H V φ m).symm
        (sliceHomEquivA_apply A B hX M H V ψ m).symm)

/-- The image of `φ` under `sliceHomAddEquiv` sends `m` to the value of `φ` over the identity
of `V` on the unit section determined by `m`. -/
lemma sliceHomAddEquiv_apply (M : ModuleCat.{u} A) (H : Mod A B hX) (V : Site A B hX)
    (φ : ((epsT A B hX).obj M).over V ⟶ H.over V) (m : M) :
    (show H.val.obj (op V) from sliceHomAddEquiv M H V φ m) =
      φ.val.app (op (Over.mk (𝟙 V))) (unitSectionAt A B hX M V m) :=
  sliceHomEquivA_apply A B hX M H V φ m

variable (P : CochainComplex (ModuleCat.{u} A) ℤ) (J : CochainComplex (Mod A B hX) ℤ)
  (V : Site A B hX)

/-- The slice universal property, between the terms of the restricted complexes. -/
abbrev sliceHomAddEquivs (p q : ℤ) :
    ((RingedSite.restrictComplex (Xs A B hX) (Fc P) V).X p ⟶
      (RingedSite.restrictComplex (Xs A B hX) J V).X q) ≃+
      (P.X p ⟶ (((secA A B hX V).mapHomologicalComplex (ComplexShape.up ℤ)).obj J).X q) :=
  sliceHomAddEquiv (P.X p) (J.X q) V

/-- The Hom complex out of the restriction of `ε^* P̃` to `V` is the Hom complex of `A`-modules
into the sections over `V`, up to the universe lift. -/
def homComplexSliceIso :
    (RingedSite.restrictComplex (Xs A B hX) (Fc P) V).HomComplex
        (RingedSite.restrictComplex (Xs A B hX) J V) ≅
      (AddCommGrpCat.uliftFunctor.{u + 1}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (P.HomComplex (((secA A B hX V).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) :=
  HomologicalComplex.Hom.isoOfComponents
    (fun n => ((cochainAddEquiv (sliceHomAddEquivs P J V) n).trans
      AddEquiv.ulift.symm).toAddCommGrpIso)
    (fun n m _ => by
      ext z
      change ULift.up (δ n m (cochainAddEquiv (sliceHomAddEquivs P J V) n z)) =
        ULift.up (cochainAddEquiv (sliceHomAddEquivs P J V) m (δ n m z))
      exact congrArg ULift.up (δ_cochainAddEquiv (sliceHomAddEquivs P J V)
        (fun p q q' f => sliceHomEquivA_comp_right A B hX (P.X p) V f (J.d q q'))
        (fun p' p q f => sliceHomEquivA_comp_left A B hX (J.X q) V (P.d p' p) f) n m z))

/-- The `(p, q)` component of the image of a cochain `z` under `homComplexSliceIso` is the image
of the `(p, q)` component of `z` under `sliceHomAddEquiv`. -/
lemma homComplexSliceIso_hom_apply (n : ℤ)
    (z : Cochain (RingedSite.restrictComplex (Xs A B hX) (Fc P) V)
      (RingedSite.restrictComplex (Xs A B hX) J V) n) (p q : ℤ) (hpq : p + n = q) :
    ((homComplexSliceIso P J V).hom.f n z).down.v p q hpq =
      sliceHomAddEquiv (P.X p) (J.X q) V (z.v p q hpq) := by
  change (cochainAddEquiv (sliceHomAddEquivs P J V) n z).v p q hpq = _
  rw [cochainAddEquiv_v]

/-- **The sections over `V` of `SheafHom^•(ε^* P̃, J)` are `Hom^•_A(P, J(V))`**, up to the
universe lift. -/
def sectionsHomIso :
    RingedSite.sectionComplex (Xs A B hX) (Tc P J) V ≅
      (AddCommGrpCat.uliftFunctor.{u + 1}.mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (P.HomComplex (((secA A B hX V).mapHomologicalComplex (ComplexShape.up ℤ)).obj J)) :=
  (RingedSite.sheafHomComplex (Xs A B hX) (Fc P) J).sectionsIso V ≪≫ homComplexSliceIso P J V

end AlgebraicGeometry.AffineEtaleDuality

end
