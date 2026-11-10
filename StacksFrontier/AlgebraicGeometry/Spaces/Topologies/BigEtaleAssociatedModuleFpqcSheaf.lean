module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.CoveringComparisonTopologies
public import StacksFrontier.AlgebraicGeometry.Spaces.Descent.QuasiCoherent.ReprFpqcFullness
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasicoherentStructureSheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModulePushforwardCompIsoAssoc
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.BigEtaleAssociatedModule

/-!
# The rule `𝓕ᵃ` satisfies the fpqc sheaf condition (Stacks 0DGN, clause (1))

Let `X` be an algebraic space over a scheme `S` and `𝓕` a quasi-coherent `𝒪_X`-module.  The rule
`𝓕ᵃ : (f : Y ⟶ X) ↦ Γ(Y, f^*𝓕)` of
`StacksFrontier/AlgebraicGeometry/Spaces/Topologies/BigEtaleAssociatedModule.lean`, a presheaf of
abelian groups on the algebraic spaces over `X`, satisfies the sheaf condition for every fpqc
covering `{Y i ⟶ Y}` of an algebraic space over `X`; a fortiori for every fppf and every étale
covering.

The proof is the source's.  Write `g : Y ⟶ X` for the structure morphism and `f i : Y i ⟶ Y` for
the members of the covering.  A section of `𝓕ᵃ` over `Y i` is a morphism
`(f i ≫ g)^*𝒪_X ⟶ (f i ≫ g)^*𝓕`; conjugating it by the comparison `(f i ≫ g)^* ≅ g^* ⋙ (f i)^*`
of Stacks 03LU turns it into a morphism `φ i : (f i)^*(g^*𝒪_X) ⟶ (f i)^*(g^*𝓕)`.  A compatible
family of sections gives a family `φ` compatible with the canonical descent data of the
quasi-coherent modules `g^*𝒪_X` and `g^*𝓕` relative to the covering, that is, a morphism of
descent data in the sense of Stacks 04W3.  By the full-faithfulness clause of Descent on Spaces,
Proposition 04W8, it descends uniquely to a morphism `g^*𝒪_X ⟶ g^*𝓕`, which is the section of
`𝓕ᵃ` over `Y` sought.

## Main results

* `AlgebraicGeometry.Space.isSheafFor_associatedPresheaf_of_isFpqcCovering`: **Stacks 0DGN,
  clause (1)**, the fpqc sheaf condition.
* `AlgebraicGeometry.Space.isSheafFor_associatedPresheaf_ofArrows_overMk`: the same for a family
  given by its members `f i : A i ⟶ Y`, from which the general case is read off.
* `AlgebraicGeometry.Space.isSheafFor_associatedPresheaf_of_isFppfCovering` and
  `AlgebraicGeometry.Space.isSheafFor_associatedPresheaf_of_isEtaleCovering`: the fppf and étale
  cases, which the source derives a fortiori.

## Implementation notes

The only geometric input is the full-faithfulness clause of Stacks 04W8, in the namespace
`AlgebraicGeometry.Space`:
`QuasiCoherentDescent.nonempty_fullyFaithful_canonicalDescentFunctor_of_isFpqcCovering`. What
remains is a coherence: the composite of the comparisons
`r^* ≅ (f i ≫ g)^* ⋙ p^*` and `(f i ≫ g)^* ≅ g^* ⋙ (f i)^*`, along one projection `p` of the
fibre product `Y i ×_Y Y j`, followed by the inverse of the same composite along the other
projection, is the canonical comparison of the descent datum
(`AlgebraicGeometry.Space.modulePullbackTriangle_conj_eq_canonicalComparison`).  It follows from
the associativity coherence of the comparisons of Stacks 03LU,
`AlgebraicGeometry.Space.modulePullbackTriangle_inv_app_assoc`.  The algebra of conjugations that
turns this coherence into the descent condition is stated for an arbitrary category
(`CategoryTheory.comp_hom_eq_hom_comp_of_conj`), so that the concrete argument only applies it.

The descent step and the sheaf condition are proved for a family of objects of `Over X` of the
form `Over.mk (k i)`, with morphisms `Over.homMk (f i)`, where `A`, `f`, `k` are arbitrary
families (`AlgebraicGeometry.Space.isSheafFor_associatedPresheaf_ofArrows_overMk`).  A family
`g : ∀ i, Y i ⟶ Y` of `Over X` is of this form up to the structure eta laws of `Over X`, and the
fpqc theorem is that statement at `A i = (Y i).left`, `f i = (g i).left`.  This keeps the
families of algebraic spaces variables wherever modules over them are compared: substituting
`fun i ↦ (g i).left` into the descent lemma would compare inverse images along
`(fun i ↦ (g i).left) i` and along `(g i).left`, which the kernel only identifies after unfolding
the inverse image functors.

## References

* [Stacks Project, Tag 0DGN](https://stacks.math.columbia.edu/tag/0DGN)
* [Stacks Project, Tag 04W8](https://stacks.math.columbia.edu/tag/04W8)
* [Stacks Project, Tag 04W3](https://stacks.math.columbia.edu/tag/04W3)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Functor Opposite

universe w v u

namespace CategoryTheory

/-- **Equal conjugates give a commutative square.**  Let `α : A₁ ⟶ A₂` and `β : B₁ ⟶ B₂` become
equal after conjugation by `c₁, c₂` and by `d₁, d₂` respectively, and let `e₁ = c₁⁻¹ ≫ d₁` and
`e₂ = c₂⁻¹ ≫ d₂` be the induced comparisons.  Then `α ≫ e₂ = e₁ ≫ β`. -/
theorem comp_hom_eq_hom_comp_of_conj {C : Type*} [Category C] {Z₁ Z₂ A₁ A₂ B₁ B₂ : C}
    (c₁ : Z₁ ≅ A₁) (c₂ : Z₂ ≅ A₂) (d₁ : Z₁ ≅ B₁) (d₂ : Z₂ ≅ B₂)
    (α : A₁ ⟶ A₂) (β : B₁ ⟶ B₂) (e₁ : A₁ ≅ B₁) (e₂ : A₂ ≅ B₂)
    (h₁ : c₁.symm ≪≫ d₁ = e₁) (h₂ : c₂.symm ≪≫ d₂ = e₂)
    (h : c₁.hom ≫ α ≫ c₂.inv = d₁.hom ≫ β ≫ d₂.inv) :
    α ≫ e₂.hom = e₁.hom ≫ β := by
  subst h₁ h₂
  rw [← cancel_epi c₁.hom]
  simp [reassoc_of% h]

/-- Conjugating `L.map (e₁⁻¹ ≫ x ≫ e₂)` by `t₁ ≪≫ L.mapIso e₁` and `t₂ ≪≫ L.mapIso e₂` is
conjugating `L.map x` by `t₁` and `t₂`. -/
theorem Iso.trans_mapIso_conj {C D : Type*} [Category C] [Category D] (L : C ⥤ D)
    {Z₁ Z₂ : D} {M₁ M₂ A₁ A₂ : C} (t₁ : Z₁ ≅ L.obj M₁) (t₂ : Z₂ ≅ L.obj M₂) (e₁ : M₁ ≅ A₁)
    (e₂ : M₂ ≅ A₂) (x : M₁ ⟶ M₂) :
    (t₁ ≪≫ L.mapIso e₁).hom ≫ L.map (e₁.inv ≫ x ≫ e₂.hom) ≫ (t₂ ≪≫ L.mapIso e₂).inv =
      t₁.hom ≫ L.map x ≫ t₂.inv := by
  simp

/-- Conjugating by `e, e'` undoes conjugating by their inverses. -/
theorem Iso.hom_comp_conj_comp_inv {C : Type*} [Category C] {M N A B : C} (e : M ≅ A)
    (e' : N ≅ B) (x : M ⟶ N) : e.hom ≫ (e.inv ≫ x ≫ e'.hom) ≫ e'.inv = x := by
  simp

/-- Conjugating by the inverses of `e, e'` undoes conjugating by them. -/
theorem Iso.inv_comp_conj_comp_hom {C : Type*} [Category C] {M N A B : C} (e : M ≅ A)
    (e' : N ≅ B) (y : A ⟶ B) : e.inv ≫ (e.hom ≫ y ≫ e'.inv) ≫ e'.hom = y := by
  simp

/-- A morphism conjugated by `e, e'` is `x` exactly when it is `x` conjugated by their
inverses. -/
theorem Iso.hom_comp_comp_inv_eq_iff {C : Type*} [Category C] {M N A B : C} (e : M ≅ A)
    (e' : N ≅ B) (y : A ⟶ B) (x : M ⟶ N) :
    e.hom ≫ y ≫ e'.inv = x ↔ y = e.inv ≫ x ≫ e'.hom := by
  constructor <;> rintro rfl <;> simp

/-- The underlying map of a conjugation of Hom groups is the conjugation.  Stated for abstract
categories, where it holds by definition at no cost; for the module categories of algebraic
spaces the same identification is expensive to check by unfolding. -/
theorem Functor.forget_map_conjGrpHom_eq_app {C D₁ D₂ : Type*} [Category.{w} C] [Category.{w} D₁]
    [Category.{w} D₂] [Preadditive D₁] [Preadditive D₂] {P₁ : C ⥤ D₁} {P₂ : C ⥤ D₂} {L : D₁ ⥤ D₂}
    [L.Additive] (e : P₂ ≅ P₁ ⋙ L) (M N : C) (α : P₁.obj M ⟶ P₁.obj N) :
    (forget AddCommGrpCat).map (conjGrpHom e M N) α = (e.app M).hom ≫ L.map α ≫ (e.app N).inv :=
  rfl

end CategoryTheory

namespace AlgebraicGeometry.Space

open QuasiCoherentDescent

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The comparison `r^*M ≅ p^*(k^*M)` of Stacks 03LU at a factorization `p ≫ k = r`, in the
spelling of the descent library, is the comparison `AlgebraicGeometry.Space.modulePullbackTriangle`
at `M`. -/
theorem pullbackComparison_eq_modulePullbackTriangle_app {P Q A : AlgebraicSpaces B S hS}
    (p : P ⟶ Q) (k : Q ⟶ A) (r : P ⟶ A) (hr : p ≫ k = r) (M : Modules.{u, u} B S hS A.1 A.2) :
    pullbackComparison B S hS p k r hr M =
      (modulePullbackTriangle B S hS hr).app M := by
  subst hr
  rw [pullbackComparison_rfl, modulePullbackTriangle_rfl]
  exact Iso.ext rfl

/-- **The canonical comparison of a descent datum, through the comparisons of Stacks 03LU.**
For `a : P ⟶ Q`, `b : P ⟶ R` with `a ≫ fi = b ≫ fj`, and a further `q : A ⟶ Z`, identify
`r^*M` with `a^*fi^*q^*M` and with `b^*fj^*q^*M` through the comparisons of inverse images of
Stacks 03LU, where `r` is the common composite to `Z`.  The first identification inverted,
followed by the second, is the canonical comparison of the two inverse images of `q^*M`.

Both identifications are factored through the comparison for the one morphism `a ≫ fi`, by the
associativity coherence `AlgebraicGeometry.Space.modulePullbackTriangle_inv_app_assoc`, so the
factor `r^* ≅ q^* ⋙ (a ≫ fi)^*` they share cancels. -/
theorem modulePullbackTriangle_conj_eq_canonicalComparison
    {P Q R A Z : AlgebraicSpaces B S hS} (a : P ⟶ Q) (b : P ⟶ R) (fi : Q ⟶ A) (fj : R ⟶ A)
    (q : A ⟶ Z) {ki : Q ⟶ Z} {kj : R ⟶ Z} {r : P ⟶ Z} (h : a ≫ fi = b ≫ fj)
    (hi : fi ≫ q = ki) (hj : fj ≫ q = kj) (hri : a ≫ ki = r) (hrj : b ≫ kj = r)
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    ((modulePullbackTriangle B S hS hri).app M ≪≫
        (modulePullback B S hS a).mapIso ((modulePullbackTriangle B S hS hi).app M)).symm ≪≫
      ((modulePullbackTriangle B S hS hrj).app M ≪≫
        (modulePullback B S hS b).mapIso ((modulePullbackTriangle B S hS hj).app M)) =
    canonicalComparison a b fi fj h ((modulePullback B S hS q).obj M) := by
  have hkr : (a ≫ fi) ≫ q = r := by rw [Category.assoc, hi, hri]
  have key {T : AlgebraicSpaces B S hS} {k : P ⟶ A} {kt : T ⟶ Z} (c : P ⟶ T) (g : T ⟶ A)
      (hk : c ≫ g = k) (hg : g ≫ q = kt) (hc : c ≫ kt = r) (hkr : k ≫ q = r) :
      (modulePullbackTriangle B S hS hc).app M ≪≫
        (modulePullback B S hS c).mapIso ((modulePullbackTriangle B S hS hg).app M) =
      (modulePullbackTriangle B S hS hkr).app M ≪≫
        (modulePullbackTriangle B S hS hk).app ((modulePullback B S hS q).obj M) :=
    Iso.ext ((Iso.inv_eq_inv _ _).1 (modulePullbackTriangle_inv_app_assoc B S hS hk hg hc hkr M))
  rw [key a fi rfl hi hri hkr, key b fj h.symm hj hrj hkr,
    canonicalComparison_eq_pullbackComparison B S hS a b fi fj h (a ≫ fi) rfl h.symm,
    pullbackComparison_eq_modulePullbackTriangle_app,
    pullbackComparison_eq_modulePullbackTriangle_app, Iso.trans_symm, Iso.trans_assoc,
    Iso.symm_self_id_assoc]

/-- `AlgebraicGeometry.Space.modulePullbackTriangle_conj_eq_canonicalComparison` in the spelling
of the descent library, whose comparisons
`AlgebraicGeometry.Space.QuasiCoherentDescent.pullbackComparison` are stated between iterated
inverse images rather than inverse images along composite functors. -/
theorem pullbackComparison_conj_eq_canonicalComparison
    {P Q R A Z : AlgebraicSpaces B S hS} (a : P ⟶ Q) (b : P ⟶ R) (fi : Q ⟶ A) (fj : R ⟶ A)
    (q : A ⟶ Z) (ki : Q ⟶ Z) (kj : R ⟶ Z) (r : P ⟶ Z) (h : a ≫ fi = b ≫ fj)
    (hi : fi ≫ q = ki) (hj : fj ≫ q = kj) (hri : a ≫ ki = r) (hrj : b ≫ kj = r)
    (M : Modules.{u, u} B S hS Z.1 Z.2) :
    (pullbackComparison B S hS a ki r hri M ≪≫
        (modulePullback B S hS a).mapIso (pullbackComparison B S hS fi q ki hi M)).symm ≪≫
      (pullbackComparison B S hS b kj r hrj M ≪≫
        (modulePullback B S hS b).mapIso (pullbackComparison B S hS fj q kj hj M)) =
    canonicalComparison a b fi fj h ((modulePullback B S hS q).obj M) := by
  simp only [pullbackComparison_eq_modulePullbackTriangle_app]
  exact modulePullbackTriangle_conj_eq_canonicalComparison B S hS a b fi fj q h hi hj hri hrj M

/-- The restriction maps of `𝓕ᵃ`, forgetting the group structure: restriction along a morphism
`m : Z' ⟶ Z` of algebraic spaces over `X` is conjugation by the comparison
`Z'^* ≅ Z^* ⋙ m^*` of Stacks 03LU. -/
theorem associatedPresheaf_forget_map_apply {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) {Z Z' : Over X} (m : Z' ⟶ Z)
    (α : (modulePullback B S hS Z.hom).obj
        (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) ⟶
      (modulePullback B S hS Z.hom).obj F) :
    (associatedPresheaf F ⋙ forget AddCommGrpCat).map m.op α =
      (pullbackComparison B S hS (A := X) m.left Z.hom Z'.hom (Over.w m)
          (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2)).hom ≫
        (modulePullback B S hS m.left).map α ≫
        (pullbackComparison B S hS (A := X) m.left Z.hom Z'.hom (Over.w m) F).inv := by
  rw [pullbackComparison_eq_modulePullbackTriangle_app,
    pullbackComparison_eq_modulePullbackTriangle_app]
  exact Functor.forget_map_conjGrpHom_eq_app (modulePullbackTriangle B S hS (Over.w m))
    (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) F α

/-- `AlgebraicGeometry.Space.associatedPresheaf_forget_map_apply` for a morphism out of
`Over.mk r`, with the factorization `m.left ≫ Z.hom = r` presented through any morphism
`p = m.left`. -/
theorem associatedPresheaf_forget_map_apply_of_eq {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) {Z : Over X} {W : AlgebraicSpaces B S hS} (r : W ⟶ X)
    (m : Over.mk r ⟶ Z) (p : W ⟶ Z.left) (hp : m.left = p) (hr : p ≫ Z.hom = r)
    (α : (modulePullback B S hS Z.hom).obj
        (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) ⟶
      (modulePullback B S hS Z.hom).obj F) :
    (associatedPresheaf F ⋙ forget AddCommGrpCat).map m.op α =
      (pullbackComparison B S hS (A := X) p Z.hom r hr
          (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2)).hom ≫
        (modulePullback B S hS p).map α ≫
        (pullbackComparison B S hS (A := X) p Z.hom r hr F).inv := by
  subst hp
  rw [pullbackComparison_eq_modulePullbackTriangle_app,
    pullbackComparison_eq_modulePullbackTriangle_app]
  exact Functor.forget_map_conjGrpHom_eq_app (modulePullbackTriangle B S hS hr)
    (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) F α

/-- The conjugation identity behind
`AlgebraicGeometry.Space.descent_square_of_conj_eq`: conjugating the conjugated morphism
`fi^*(q^*O) ⟶ fi^*(q^*F)` back along `p₁` recovers the restriction of `xi`, and likewise for `xj`,
so equal restrictions give equal conjugates. -/
theorem modulePullback_conj_eq_of_conj_eq {P Ai Aj Y₀ X : AlgebraicSpaces B S hS} (p₁ : P ⟶ Ai)
    (p₂ : P ⟶ Aj) (fi : Ai ⟶ Y₀) (fj : Aj ⟶ Y₀) (q : Y₀ ⟶ X) (ki : Ai ⟶ X) (kj : Aj ⟶ X)
    (r : P ⟶ X) (hi : fi ≫ q = ki) (hj : fj ≫ q = kj)
    (hri : p₁ ≫ ki = r) (hrj : p₂ ≫ kj = r) (O F : Modules.{u, u} B S hS X.1 X.2)
    (xi : (modulePullback B S hS ki).obj O ⟶ (modulePullback B S hS ki).obj F)
    (xj : (modulePullback B S hS kj).obj O ⟶ (modulePullback B S hS kj).obj F)
    (hc : ((pullbackComparison B S hS p₁ ki r hri) O).hom ≫ (modulePullback B S hS p₁).map xi ≫
        ((pullbackComparison B S hS p₁ ki r hri) F).inv =
      ((pullbackComparison B S hS p₂ kj r hrj) O).hom ≫ (modulePullback B S hS p₂).map xj ≫
        ((pullbackComparison B S hS p₂ kj r hrj) F).inv) :
    ((pullbackComparison B S hS p₁ ki r hri) O ≪≫
      (modulePullback B S hS p₁).mapIso ((pullbackComparison B S hS fi q ki hi) O)).hom ≫
      (modulePullback B S hS p₁).map (((pullbackComparison B S hS fi q ki hi) O).inv ≫ xi ≫
          ((pullbackComparison B S hS fi q ki hi) F).hom) ≫
      ((pullbackComparison B S hS p₁ ki r hri) F ≪≫
      (modulePullback B S hS p₁).mapIso ((pullbackComparison B S hS fi q ki hi) F)).inv =
    ((pullbackComparison B S hS p₂ kj r hrj) O ≪≫
      (modulePullback B S hS p₂).mapIso ((pullbackComparison B S hS fj q kj hj) O)).hom ≫
      (modulePullback B S hS p₂).map (((pullbackComparison B S hS fj q kj hj) O).inv ≫ xj ≫
          ((pullbackComparison B S hS fj q kj hj) F).hom) ≫
      ((pullbackComparison B S hS p₂ kj r hrj) F ≪≫
      (modulePullback B S hS p₂).mapIso ((pullbackComparison B S hS fj q kj hj) F)).inv :=
   ((Iso.trans_mapIso_conj (modulePullback B S hS p₁) ((pullbackComparison B S hS p₁ ki r hri) O)
        ((pullbackComparison B S hS p₁ ki r hri) F) ((pullbackComparison B S hS fi q ki hi) O)
        ((pullbackComparison B S hS fi q ki hi) F) xi).trans
      (hc.trans (Iso.trans_mapIso_conj (modulePullback B S hS p₂)
        ((pullbackComparison B S hS p₂ kj r hrj) O) ((pullbackComparison B S hS p₂ kj r hrj) F)
        ((pullbackComparison B S hS fj q kj hj) O) ((pullbackComparison B S hS fj q kj hj) F)
        xj).symm))

/-- **Equal restrictions give a morphism of descent data, for one pair of members.**  Let
`fi : Ai ⟶ Y₀` and `fj : Aj ⟶ Y₀` be two members of a family over `Y₀`, `q : Y₀ ⟶ X`, and
`p₁ : P ⟶ Ai`, `p₂ : P ⟶ Aj` with `p₁ ≫ fi = p₂ ≫ fj`.  Two morphisms `xi : ki^*O ⟶ ki^*F` and
`xj : kj^*O ⟶ kj^*F` over the composites `ki = fi ≫ q` and `kj = fj ≫ q` which have equal
restrictions to `P` (conjugation by the comparisons of Stacks 03LU along `p₁` and `p₂`) give,
after conjugation into morphisms `fi^*(q^*O) ⟶ fi^*(q^*F)` and `fj^*(q^*O) ⟶ fj^*(q^*F)`, a
commutative square with the canonical comparisons of the descent datum. -/
theorem descent_square_of_conj_eq {P Ai Aj Y₀ X : AlgebraicSpaces B S hS} (p₁ : P ⟶ Ai)
    (p₂ : P ⟶ Aj) (fi : Ai ⟶ Y₀) (fj : Aj ⟶ Y₀) (q : Y₀ ⟶ X) (ki : Ai ⟶ X) (kj : Aj ⟶ X)
    (r : P ⟶ X) (hpair : p₁ ≫ fi = p₂ ≫ fj) (hi : fi ≫ q = ki) (hj : fj ≫ q = kj)
    (hri : p₁ ≫ ki = r) (hrj : p₂ ≫ kj = r) (O F : Modules.{u, u} B S hS X.1 X.2)
    (xi : (modulePullback B S hS ki).obj O ⟶ (modulePullback B S hS ki).obj F)
    (xj : (modulePullback B S hS kj).obj O ⟶ (modulePullback B S hS kj).obj F)
    (hc : ((pullbackComparison B S hS p₁ ki r hri) O).hom ≫ (modulePullback B S hS p₁).map xi ≫
        ((pullbackComparison B S hS p₁ ki r hri) F).inv =
      ((pullbackComparison B S hS p₂ kj r hrj) O).hom ≫ (modulePullback B S hS p₂).map xj ≫
        ((pullbackComparison B S hS p₂ kj r hrj) F).inv) :
    (modulePullback B S hS p₁).map (((pullbackComparison B S hS fi q ki hi) O).inv ≫ xi ≫
          ((pullbackComparison B S hS fi q ki hi) F).hom) ≫
        (canonicalComparison p₁ p₂ fi fj hpair
          ((modulePullback B S hS q).obj F)).hom =
      (canonicalComparison p₁ p₂ fi fj hpair
          ((modulePullback B S hS q).obj O)).hom ≫
        (modulePullback B S hS p₂).map (((pullbackComparison B S hS fj q kj hj) O).inv ≫ xj ≫
          ((pullbackComparison B S hS fj q kj hj) F).hom) :=
  comp_hom_eq_hom_comp_of_conj
    ((pullbackComparison B S hS p₁ ki r hri) O ≪≫
      (modulePullback B S hS p₁).mapIso ((pullbackComparison B S hS fi q ki hi) O))
    ((pullbackComparison B S hS p₁ ki r hri) F ≪≫
      (modulePullback B S hS p₁).mapIso ((pullbackComparison B S hS fi q ki hi) F))
    ((pullbackComparison B S hS p₂ kj r hrj) O ≪≫
      (modulePullback B S hS p₂).mapIso ((pullbackComparison B S hS fj q kj hj) O))
    ((pullbackComparison B S hS p₂ kj r hrj) F ≪≫
      (modulePullback B S hS p₂).mapIso ((pullbackComparison B S hS fj q kj hj) F))
    _ _ _ _
    (pullbackComparison_conj_eq_canonicalComparison B S hS p₁ p₂ fi fj q ki kj r hpair hi hj
      hri hrj O)
    (pullbackComparison_conj_eq_canonicalComparison B S hS p₁ p₂ fi fj q ki kj r hpair hi hj
      hri hrj F)
    (modulePullback_conj_eq_of_conj_eq B S hS p₁ p₂ fi fj q ki kj r hi hj hri hrj O F xi xj
      hc)

/-- A family of morphisms of the components of two canonical descent data which commutes with
their pairwise isomorphisms, as a morphism of descent data. -/
def descentDatumHomOfFamily {Y₀ : AlgebraicSpaces B S hS} {I : Type v}
    (A : I → AlgebraicSpaces B S hS) (f : ∀ i, A i ⟶ Y₀) (M N : Modules.{u, u} B S hS Y₀.1 Y₀.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (β : ∀ i, (canonicalDescentDatum' B S hS A f M hM).F i ⟶
      (canonicalDescentDatum' B S hS A f N hN).F i)
    (hβ : ∀ i j, (modulePullback B S hS (pairFst B S hS A f i j)).map (β i) ≫
        ((canonicalDescentDatum' B S hS A f N hN).transition i j).hom =
      ((canonicalDescentDatum' B S hS A f M hM).transition i j).hom ≫
        (modulePullback B S hS (pairSnd B S hS A f i j)).map (β j)) :
    canonicalDescentDatum' B S hS A f M hM ⟶ canonicalDescentDatum' B S hS A f N hN :=
  DescentDatum.Hom.mk β hβ

/-- **Descent of morphisms of quasi-coherent modules along an fpqc covering** (the
full-faithfulness clause of Stacks 04W8, read on morphisms).  A family of morphisms
`β i : (f i)^*M ⟶ (f i)^*N` commuting with the canonical comparisons of the descent data of `M`
and `N` relative to an fpqc covering `{f i : A i ⟶ Y₀}` is the family of inverse images of
exactly one morphism `M ⟶ N`. -/
theorem existsUnique_hom_of_isFpqcCovering {Y₀ : AlgebraicSpaces B S hS} {I : Type v}
    (A : I → AlgebraicSpaces B S hS) (f : ∀ i, A i ⟶ Y₀)
    (hf : IsFpqcCovering B S hS fun i ↦ (f i).hom) (M N : Modules.{u, u} B S hS Y₀.1 Y₀.2)
    (hM : M.IsQuasicoherentOnSite) (hN : N.IsQuasicoherentOnSite)
    (β : ∀ i, (modulePullback B S hS (f i)).obj M ⟶ (modulePullback B S hS (f i)).obj N)
    (hβ : ∀ i j, (modulePullback B S hS (pairFst B S hS A f i j)).map (β i) ≫
        (canonicalComparison (pairFst B S hS A f i j) (pairSnd B S hS A f i j) (f i) (f j)
          (pair_condition B S hS A f i j) N).hom =
      (canonicalComparison (pairFst B S hS A f i j) (pairSnd B S hS A f i j) (f i) (f j)
          (pair_condition B S hS A f i j) M).hom ≫
        (modulePullback B S hS (pairSnd B S hS A f i j)).map (β j)) :
    ∃! t : M ⟶ N, ∀ i, (modulePullback B S hS (f i)).map t = β i := by
  let FF := (nonempty_fullyFaithful_canonicalDescentFunctor_of_isFpqcCovering B S hS A f hf).some
  let D : (canonicalDescentFunctor' B S hS A f).obj ⟨M, hM⟩ ⟶
      (canonicalDescentFunctor' B S hS A f).obj ⟨N, hN⟩ :=
    descentDatumHomOfFamily B S hS A f M N hM hN β fun i j ↦ by
      rw [canonicalDescentDatum'_transition, canonicalDescentDatum'_transition]
      exact hβ i j
  refine ⟨(FF.preimage D).hom, fun i ↦ congrArg (fun z ↦ DescentDatum.Hom.app z i)
    (FF.map_preimage D), fun t ht ↦ ?_⟩
  have hD : (canonicalDescentFunctor' B S hS A f).map
      (ObjectProperty.homMk t : (⟨M, hM⟩ : QuasicoherentSheaves.{u, u} B S hS Y₀.1 Y₀.2) ⟶
        ⟨N, hN⟩) = D :=
    DescentDatum.Hom.ext ht
  exact congrArg (fun z ↦ z.hom) (FF.map_injective (hD.trans (FF.map_preimage D).symm))

/-- The second projection of `A i ×_{Y₀} A j` followed by `k j` is the first projection followed
by `k i`, for a family `k i = f i ≫ q`. -/
theorem pairSnd_comp_eq_pairFst_comp {Y₀ X : AlgebraicSpaces B S hS} {I : Type v}
    (A : I → AlgebraicSpaces B S hS) (f : ∀ i, A i ⟶ Y₀) (q : Y₀ ⟶ X) (k : ∀ i, A i ⟶ X)
    (hk : ∀ i, f i ≫ q = k i) (i j : I) :
    pairSnd B S hS A f i j ≫ k j =
      pairFst B S hS A f i j ≫ k i := by
  rw [← hk i, ← hk j, ← Category.assoc, ← Category.assoc,
    pair_condition B S hS A f i j]

section FpqcSheaf

variable {B S hS} {X : AlgebraicSpaces B S hS} {I : Type v}

/-- **Morphisms over the members of an fpqc covering which agree on the pairwise fibre products
come from exactly one morphism** (Stacks 04W8, full faithfulness, read on morphisms over `X`).
Let `{f i : A i ⟶ Y₀}` be an fpqc covering, `q : Y₀ ⟶ X`, `k i = f i ≫ q`, and `O`, `F`
quasi-coherent `𝒪_X`-modules.  A family `x i : (k i)^*O ⟶ (k i)^*F` whose restrictions to
`A i ×_{Y₀} A j` along the two projections agree is, after the comparisons
`(k i)^* ≅ (f i)^* ∘ q^*` of Stacks 03LU, the family of inverse images of exactly one morphism
`q^*O ⟶ q^*F`. -/
theorem existsUnique_of_restrictions_eq {Y₀ : AlgebraicSpaces B S hS}
    (A : I → AlgebraicSpaces B S hS) (f : ∀ i, A i ⟶ Y₀) (q : Y₀ ⟶ X) (k : ∀ i, A i ⟶ X)
    (hk : ∀ i, f i ≫ q = k i) (hf : IsFpqcCovering B S hS fun i ↦ (f i).hom)
    (O F : Modules.{u, u} B S hS X.1 X.2) (hO : O.IsQuasicoherentOnSite)
    (hF : F.IsQuasicoherentOnSite)
    (x : ∀ i, (modulePullback B S hS (k i)).obj O ⟶ (modulePullback B S hS (k i)).obj F)
    (hx : ∀ i j,
      (pullbackComparison B S hS (A := X) (pairFst B S hS A f i j) (k i)
          (pairFst B S hS A f i j ≫ k i) rfl O).hom ≫
        (modulePullback B S hS (pairFst B S hS A f i j)).map (x i) ≫
        (pullbackComparison B S hS (A := X) (pairFst B S hS A f i j) (k i)
          (pairFst B S hS A f i j ≫ k i) rfl F).inv =
      (pullbackComparison B S hS (A := X) (pairSnd B S hS A f i j) (k j)
          (pairFst B S hS A f i j ≫ k i) (pairSnd_comp_eq_pairFst_comp B S hS A f q k hk i j)
          O).hom ≫
        (modulePullback B S hS (pairSnd B S hS A f i j)).map (x j) ≫
        (pullbackComparison B S hS (A := X) (pairSnd B S hS A f i j) (k j)
          (pairFst B S hS A f i j ≫ k i) (pairSnd_comp_eq_pairFst_comp B S hS A f q k hk i j)
          F).inv) :
    ∃! t : (modulePullback B S hS q).obj O ⟶ (modulePullback B S hS q).obj F,
      ∀ i, (pullbackComparison B S hS (A := X) (f i) q (k i) (hk i) O).hom ≫
        (modulePullback B S hS (f i)).map t ≫
        (pullbackComparison B S hS (A := X) (f i) q (k i) (hk i) F).inv = x i := by
  obtain ⟨t, ht, hu⟩ := existsUnique_hom_of_isFpqcCovering B S hS A f hf _ _
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS q O hO)
    (isQuasicoherentOnSite_modulePullback_of_isQuasicoherentOnSite B S hS q F hF)
    (fun i ↦ (pullbackComparison B S hS (A := X) (f i) q (k i) (hk i) O).inv ≫ x i ≫
      (pullbackComparison B S hS (A := X) (f i) q (k i) (hk i) F).hom)
    (fun i j ↦ descent_square_of_conj_eq B S hS (X := X) _ _ (f i) (f j) q (k i) (k j)
      (pairFst B S hS A f i j ≫ k i) (pair_condition B S hS A f i j) (hk i) (hk j) rfl
      (pairSnd_comp_eq_pairFst_comp B S hS A f q k hk i j) O F (x i) (x j) (hx i j))
  exact ⟨t, fun i ↦ (Iso.hom_comp_comp_inv_eq_iff _ _ _ _).2 (ht i),
    fun t' ht' ↦ hu t' fun i ↦ (Iso.hom_comp_comp_inv_eq_iff _ _ _ _).1 (ht' i)⟩

/-- `AlgebraicGeometry.Space.associatedPresheaf_forget_map_apply_of_eq` for a morphism
`m : Over.mk r ⟶ Over.mk s` between two objects given by their structure morphisms, with the
target's inverse images written along `s`. -/
theorem associatedPresheaf_forget_map_overMk_apply (F : Modules.{u, u} B S hS X.1 X.2)
    {W Q : AlgebraicSpaces B S hS} (r : W ⟶ X) (s : Q ⟶ X) (m : Over.mk r ⟶ Over.mk s)
    (p : W ⟶ Q) (hp : m.left = p) (hr : p ≫ s = r)
    (α : (modulePullback B S hS s).obj
        (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) ⟶
      (modulePullback B S hS s).obj F) :
    (associatedPresheaf F ⋙ forget AddCommGrpCat).map m.op α =
      (pullbackComparison B S hS (A := X) p s r hr
          (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2)).hom ≫
        (modulePullback B S hS p).map α ≫
        (pullbackComparison B S hS (A := X) p s r hr F).inv := by
  subst hp
  rw [pullbackComparison_eq_modulePullbackTriangle_app,
    pullbackComparison_eq_modulePullbackTriangle_app]
  exact Functor.forget_map_conjGrpHom_eq_app (modulePullbackTriangle B S hS hr)
    (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) F α

/-- **A compatible family of sections of `𝓕ᵃ` has equal restrictions to the pairwise fibre
products**, written as conjugations by the comparisons of Stacks 03LU, for the family of
objects `k i : A i ⟶ X` over `X` and morphisms `f i : A i ⟶ Y` over `X`. -/
theorem conj_eq_of_compatible {Y : Over X} (A : I → AlgebraicSpaces B S hS)
    (f : ∀ i, A i ⟶ Y.left) (k : ∀ i, A i ⟶ X) (hk : ∀ i, f i ≫ Y.hom = k i)
    (F : Modules.{u, u} B S hS X.1 X.2)
    (x : ∀ i, (modulePullback B S hS (k i)).obj
        (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) ⟶
      (modulePullback B S hS (k i)).obj F)
    (hx : Presieve.Arrows.Compatible (associatedPresheaf F ⋙ forget AddCommGrpCat)
      (fun i ↦ (Over.homMk (f i) (hk i) : Over.mk (k i) ⟶ Y)) x)
    (i j : I) :
    (pullbackComparison B S hS (A := X) (pairFst B S hS A f i j) (k i)
        (pairFst B S hS A f i j ≫ k i) rfl (SheafOfModules.unit _)).hom ≫
      (modulePullback B S hS (pairFst B S hS A f i j)).map (x i) ≫
      (pullbackComparison B S hS (A := X) (pairFst B S hS A f i j) (k i)
        (pairFst B S hS A f i j ≫ k i) rfl F).inv =
    (pullbackComparison B S hS (A := X) (pairSnd B S hS A f i j) (k j)
        (pairFst B S hS A f i j ≫ k i)
        (pairSnd_comp_eq_pairFst_comp B S hS A f Y.hom k hk i j) (SheafOfModules.unit _)).hom ≫
      (modulePullback B S hS (pairSnd B S hS A f i j)).map (x j) ≫
      (pullbackComparison B S hS (A := X) (pairSnd B S hS A f i j) (k j)
        (pairFst B S hS A f i j ≫ k i)
        (pairSnd_comp_eq_pairFst_comp B S hS A f Y.hom k hk i j) F).inv :=
  (associatedPresheaf_forget_map_overMk_apply F (pairFst B S hS A f i j ≫ k i) (k i)
      (Over.homMk (pairFst B S hS A f i j) rfl) (pairFst B S hS A f i j) rfl rfl (x i)).symm.trans
    ((hx i j (Over.mk (pairFst B S hS A f i j ≫ k i)) (Over.homMk (pairFst B S hS A f i j) rfl)
        (Over.homMk (pairSnd B S hS A f i j)
          (pairSnd_comp_eq_pairFst_comp B S hS A f Y.hom k hk i j))
        (Over.OverMorphism.ext (pair_condition B S hS A f i j))).trans
      (associatedPresheaf_forget_map_overMk_apply F (pairFst B S hS A f i j ≫ k i) (k j)
        (Over.homMk (pairSnd B S hS A f i j)
          (pairSnd_comp_eq_pairFst_comp B S hS A f Y.hom k hk i j))
        (pairSnd B S hS A f i j) rfl
        (pairSnd_comp_eq_pairFst_comp B S hS A f Y.hom k hk i j) (x j)))

/-- **`𝓕ᵃ` satisfies the sheaf condition for an fpqc covering given by its members.**  Let
`f i : A i ⟶ Y` be morphisms of algebraic spaces over `X` (the source `A i` lying over `X`
through `k i = f i ≫ (Y ⟶ X)`) forming an fpqc covering.  Then `𝓕ᵃ` satisfies the sheaf
condition for the family `{(A i, k i) ⟶ Y}` of objects of `Over X`.

A compatible family of sections over the `A i` is, after conjugation by the comparisons of
Stacks 03LU, a morphism of the canonical descent data, and it descends uniquely by the
full-faithfulness clause of Stacks 04W8
(`AlgebraicGeometry.Space.existsUnique_of_restrictions_eq`). -/
theorem isSheafFor_associatedPresheaf_ofArrows_overMk {Y : Over X}
    (F : Modules.{u, u} B S hS X.1 X.2) [hF : F.IsQuasicoherentOnSite]
    (A : I → AlgebraicSpaces B S hS) (f : ∀ i, A i ⟶ Y.left) (k : ∀ i, A i ⟶ X)
    (hk : ∀ i, f i ≫ Y.hom = k i) (hf : IsFpqcCovering B S hS fun i ↦ (f i).hom) :
    (Presieve.ofArrows (fun i ↦ Over.mk (k i))
        fun i ↦ (Over.homMk (f i) (hk i) : Over.mk (k i) ⟶ Y)).IsSheafFor
      (associatedPresheaf F ⋙ forget AddCommGrpCat) := by
  rw [Presieve.isSheafFor_arrows_iff]
  intro x hx
  let x' : ∀ i, (modulePullback B S hS (k i)).obj
      (SheafOfModules.unit _ : Modules.{u, u} B S hS X.1 X.2) ⟶
      (modulePullback B S hS (k i)).obj F := x
  obtain ⟨t, ht, hu⟩ := existsUnique_of_restrictions_eq A f Y.hom k hk hf
    (SheafOfModules.unit _) F (SheafOfModules.isQuasicoherentOnSite_unit _) hF x'
    (conj_eq_of_compatible A f k hk F x' hx)
  refine ⟨t, fun i ↦ ?_, fun t' ht' ↦ hu t' fun i ↦ ?_⟩
  · exact (associatedPresheaf_forget_map_apply_of_eq B S hS F (k i) (Over.homMk (f i) (hk i))
      (f i) rfl (hk i) t).trans (ht i)
  · exact (associatedPresheaf_forget_map_apply_of_eq B S hS F (k i) (Over.homMk (f i) (hk i))
      (f i) rfl (hk i) t').symm.trans (ht' i)

/-- **Stacks 0DGN, clause (1): `𝓕ᵃ` is an fpqc sheaf.**  For a quasi-coherent `𝒪_X`-module `𝓕`
on an algebraic space `X` over `S`, the rule `𝓕ᵃ : (f : Y ⟶ X) ↦ Γ(Y, f^*𝓕)`
(`AlgebraicGeometry.Space.associatedPresheaf`) satisfies the sheaf condition for every family
`{Y i ⟶ Y}` of morphisms of algebraic spaces over `X` which is an fpqc covering of `Y`.

This is `AlgebraicGeometry.Space.isSheafFor_associatedPresheaf_ofArrows_overMk` for the members
`(g i).left` of the family, each `Y i` being the object `Over.mk (Y i).hom` of `Over X`. -/
@[stacks 0DGN "(1): for 𝓕 a quasi-coherent 𝒪_X-module, 𝓕ᵃ satisfies the sheaf condition for \
every fpqc covering {U_i → U} of an object of (Spaces/X)_étale; the fppf and étale cases are \
isSheafFor_associatedPresheaf_of_isFppfCovering and \
isSheafFor_associatedPresheaf_of_isEtaleCovering"]
theorem isSheafFor_associatedPresheaf_of_isFpqcCovering {Y : Over X} {Yi : I → Over X}
    (g : ∀ i, Yi i ⟶ Y) (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (hg : IsFpqcCovering B S hS fun i ↦ (g i).left.hom) :
    (Presieve.ofArrows Yi g).IsSheafFor (associatedPresheaf F ⋙ forget AddCommGrpCat) :=
  isSheafFor_associatedPresheaf_ofArrows_overMk F (fun i ↦ (Yi i).left) (fun i ↦ (g i).left)
    (fun i ↦ (Yi i).hom) (fun i ↦ Over.w (g i)) hg

end FpqcSheaf

/-- **Stacks 0DGN, clause (1), fppf coverings**: the rule `𝓕ᵃ` satisfies the sheaf condition
for every fppf covering of an algebraic space over `X`. -/
theorem isSheafFor_associatedPresheaf_of_isFppfCovering {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (Y : Over X) {I : Type v} {Yi : I → Over X} (g : ∀ i, Yi i ⟶ Y)
    (hg : IsFppfCovering B S hS (fun i ↦ (Yi i).left.1) fun i ↦ (g i).left.hom) :
    (Presieve.ofArrows Yi g).IsSheafFor (associatedPresheaf F ⋙ forget AddCommGrpCat) :=
  isSheafFor_associatedPresheaf_of_isFpqcCovering g F
    (isFpqcCovering_of_isFppfCovering _ _ _ _ _ hg)

/-- **Stacks 0DGN, clause (1), étale coverings**: the rule `𝓕ᵃ` satisfies the sheaf condition
for every étale covering of an algebraic space over `X`. -/
theorem isSheafFor_associatedPresheaf_of_isEtaleCovering {X : AlgebraicSpaces B S hS}
    (F : Modules.{u, u} B S hS X.1 X.2) [F.IsQuasicoherentOnSite]
    (Y : Over X) {I : Type v} {Yi : I → Over X} (g : ∀ i, Yi i ⟶ Y)
    (hg : IsEtaleCovering B S hS (fun i ↦ (Yi i).left.1) fun i ↦ (g i).left.hom) :
    (Presieve.ofArrows Yi g).IsSheafFor (associatedPresheaf F ⋙ forget AddCommGrpCat) :=
  isSheafFor_associatedPresheaf_of_isFpqcCovering g F
    (isFpqcCovering_of_isEtaleCovering _ _ _ _ _ hg)

end AlgebraicGeometry.Space

end
