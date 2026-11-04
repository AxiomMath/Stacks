module

public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseThreeMorphism
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ClauseTwoProof
public import StacksFrontier.AlgebraicGeometry.Constructions.ProjChartGradedTriple
public import StacksFrontier.AlgebraicGeometry.RelativeProjInvertibleMorphism.ThetaClauseOne

/-!
# The triples of Stacks Tag 01O9, and the properties that characterize them

Let `S` be a scheme, `𝒜` a quasi-coherent graded `𝒪_S`-algebra, `f : X ⟶ S` a morphism, `ℒ` an
invertible `𝒪_X`-module and `ψ : f^*𝒜 ⟶ ⨁_d ℒ^{⊗ d}` a homomorphism of graded algebras.
[Stacks, Tag 01O9] constructs `r_{ℒ,ψ} : U(ψ) ⟶ Proj_S(𝒜)` and
`θ : r_{ℒ,ψ}^*(⨁_{d ≥ 0} 𝒪(d)) ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}|_{U(ψ)}` and says they are *characterized*
by its properties (1), (2) and (3). This file sets up the objects that sentence quantifies over.

## Main definitions

* `GradedNonnegHom B C`: maps of graded algebras `⨁_{d ≥ 0} B_d ⟶ ⨁_{d ≥ 0} C_d`;
  `GradedNonnegHom.ofHom` is the part in degrees `≥ 0` of a map of `ℤ`-graded algebras.
* `Triple A L`: the triples `(U', r', θ')` — an open `U'` of `X`, a morphism
  `r' : U' ⟶ Proj_S(𝒜)` and a map of graded `𝒪_{U'}`-algebras
  `θ' : r'^*(⨁_{d ≥ 0} 𝒪_{Proj_S(𝒜)}(d)) ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}|_{U'}`.
* `Triple.IsClauseOne`, `Triple.IsClauseTwo`, `Triple.IsClauseThree`: properties (1), (2) and (3)
  of the tag for such a triple, each meaningful for an arbitrary triple.
* `Triple.IsTriple`: all three.
* `Triple.canonical`: the triple `(U(ψ), r_{ℒ,ψ}, θ)`.

## Main results

* `Triple.coveringOpen_eq_of_isClauseThree`: property (3) forces the open to be `U(ψ)`.
* `Triple.exists_eq_of_isClauseThree`: property (3) forces the open and the morphism to be
  `U(ψ)` and `r_{ℒ,ψ}`.
* `Triple.isClauseOne_iff`: property (1) for `(U(ψ), r_{ℒ,ψ}, θ')` in the form of
  `…GradedPowerMap.theta_clauseOne`; `Triple.isClauseOne_canonical`,
  `Triple.isClauseTwo_canonical`.

Property (3) for `(U(ψ), r_{ℒ,ψ}, θ)` is `…GradedPowerMap.isClauseThree_theta`, and the
characterization is `…Triple.eq_canonical`, in
`StacksFrontier/AlgebraicGeometry/RelativeProjInvertibleMorphism/TripleUnique.lean`.

## References

* [Stacks Project, Tag 01O9](https://stacks.math.columbia.edu/tag/01O9)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory Opposite TopologicalSpace
open Stacks.RingedSpace
open Stacks.AlgebraicGeometry.RelativeProjBridge
open Stacks.AlgebraicGeometry.RelativeProj
open Stacks.AlgebraicGeometry.RelativeProjQcohSheaf
open Stacks.AlgebraicGeometry.CoherentMulSections (powCompare)
open Stacks.AmpleProjectiveImmersion (tensorPowerModule)
open Stacks.AlgebraicGeometry.ProjChartGradedTriple (laurentOn)

universe u

namespace Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

attribute [local instance] Stacks.SheafOfModules.monoidalCategoryPresheafOfModules
  Stacks.SheafOfModules.symmetricCategoryPresheafOfModules
  Stacks.SheafInternalHom.isMonoidal_localIso
  Stacks.SheafInternalHom.isLocalization_sheafify Stacks.SheafInternalHom.monoidalCategory
  Stacks.SheafInternalHom.sheafifyMonoidal Stacks.SheafInternalHom.braidedCategory
  Stacks.SheafInternalHom.schemeMonoidalCategory
  Stacks.SectionRingGeometric.schemeBraidedCategory

/-! ### Maps of graded algebras in degrees `≥ 0` -/

section NonnegHom

variable {Y : Scheme.{u}} (B C : SheafOfModules.GradedAlgebra.{u, u} Y.ringCatSheaf)

/-- **A map of graded algebras in degrees `≥ 0`**: for sheaves of `ℤ`-graded `𝒪_Y`-algebras `B`
and `C`, a map `⨁_{d ≥ 0} B_d ⟶ ⨁_{d ≥ 0} C_d` of graded `𝒪_Y`-algebras — a morphism of sheaves
of modules in each degree `d ≥ 0`, preserving products of homogeneous local sections. -/
structure GradedNonnegHom where
  /-- The morphism of sheaves of modules in each degree `d ≥ 0`. -/
  app (d : ℕ) : B.piece d ⟶ C.piece d
  /-- Products of homogeneous local sections are preserved. -/
  map_mul (d e : ℕ) (U : Y.Opensᵒᵖ) (x : (B.piece d).val.obj U) (y : (B.piece e).val.obj U) :
    (app (d + e)).val.app U ((B.mul d e).app U x y) =
      (C.mul d e).app U ((app d).val.app U x) ((app e).val.app U y)

variable {B C}

/-- Two maps in degrees `≥ 0` agree as soon as their components do. -/
@[ext]
theorem GradedNonnegHom.ext {φ ψ : GradedNonnegHom B C} (h : ∀ d : ℕ, φ.app d = ψ.app d) :
    φ = ψ := by
  cases φ; cases ψ; congr; funext d; exact h d

/-- **The part in degrees `≥ 0`** of a map of sheaves of `ℤ`-graded algebras. -/
def GradedNonnegHom.ofHom (θ : SheafOfModules.GradedAlgebra.Hom B C) : GradedNonnegHom B C where
  app d := θ.app d
  map_mul d e U x y := θ.map_mul d e U x y

/-- The component in degree `d ≥ 0` of the part in degrees `≥ 0` of `θ` is the component of `θ`
in degree `d`. -/
@[simp] theorem GradedNonnegHom.ofHom_app (θ : SheafOfModules.GradedAlgebra.Hom B C) (d : ℕ) :
    (GradedNonnegHom.ofHom θ).app d = θ.app d := rfl

end NonnegHom

variable {S X : Scheme.{u}} (A : SheafGradedAlgebra.{u} S) (L : X.Modules)
  [Stacks.Ample.IsInvertibleModule X L]

/-- **The triples `(U', r', θ')` of [Stacks, Tag 01O9]**: an open `U'` of `X`, a morphism of
schemes `r' : U' ⟶ Proj_S(𝒜)` and a map of graded `𝒪_{U'}`-algebras
`θ' : r'^*(⨁_{d ≥ 0} 𝒪_{Proj_S(𝒜)}(d)) ⟶ ⨁_{d ≥ 0} ℒ^{⊗ d}|_{U'}`. -/
abbrev Triple : Type _ :=
  Σ U' : X.Opens, Σ r' : U'.toScheme ⟶ (relativeProj A).scheme,
    GradedNonnegHom
      (Stacks.Conormal.gradedPullback r' (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra)
      (laurentOn L U')

namespace Triple

attribute [local irreducible] GradedPowerMap.globalMorphism
  Stacks.AlgebraicGeometry.ProjChartFullGraded.GradedSections.glued

variable {A L} {f : X ⟶ S}

/-- **Property (1) of [Stacks, Tag 01O9]** for a triple `(U', r', θ')`: for every open `V` of the
base, every `d ≥ 0` and every `a ∈ 𝒜_d(V)`, `θ'` carries the pullback along `r'` of the section of
`𝒪(d)` over `π^{-1}(V)` attached to `a` to `ψ(a)`, both read over `f^{-1}(V) ∩ r'^{-1}(π^{-1}(V))`
(which is `f^{-1}(V) ∩ U'` as soon as `r'` lies over `S`). -/
def IsClauseOne (P : GradedPowerMap A f) (t : Triple A P.L) : Prop :=
  ∀ (V : S.Opens) (d : ℕ) (a : Γ(A.piece (d : ℤ), V)),
    ((tensorPowerModule X P.L (d : ℤ)).restrict t.1.ι).presheaf.map
        (homOfLE (inf_le_left : t.2.1 ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V) ⊓ t.1.ι ⁻¹ᵁ (f ⁻¹ᵁ V)
          ≤ t.2.1 ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V))).op
        ((t.2.2.app d).val.app (op (t.2.1 ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
          (pullbackUnit t.2.1.toLRSHom.toShHom
            ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra.piece (d : ℤ))
            (op ((relativeProj A).toBase ⁻¹ᵁ V))
            (((GluedTwistAlgebra.twistDataOfGradedAlgebra A).ψ d).app V a)))
      = (tensorPowerModule X P.L (d : ℤ)).presheaf.map
          (homOfLE ((Scheme.Hom.image_mono _ inf_le_right).trans
            (t.1.ι.image_preimage_le (f ⁻¹ᵁ V)))).op
          ((powCompare P.L d).hom.app (f ⁻¹ᵁ V) (P.value d V a))

/-- **Property (2) of [Stacks, Tag 01O9]** for a triple `(U', r', θ')`: for every `k ≥ 1` and every
open `W ⊆ X` on which `ψ_k|_W : f^*𝒜_k|_W ⟶ ℒ^{⊗ k}|_W` is surjective, `W` lies in `U'` and the
restriction of `r'` to `W` is the morphism `W ⟶ Proj_S(𝒜)` which the construction of the relative
homogeneous spectrum attaches to `(k, f|_W, ℒ^{⊗ k}|_W, ψ|_W)`. -/
def IsClauseTwo (ψ : Twisting f (situationAlgebra A) 1 L) (t : Triple A L) : Prop :=
  ∀ {k : ℕ} (hk : 0 < k) (W : X.Opens) [Epi ((ψ.pullback W.ι).app (k : ℤ))],
    ∃ h : W ≤ t.1, X.homOfLE h ≫ t.2.1
      = F.classifyingMorphism A (F.mk (W.ι ≫ f) (by exact_mod_cast hk) (restrictQuadruple ψ W k))

/-- **The source of `θ'` over the piece of `U'` over an affine open `V` of the base, read as the
source of [Stacks, Tag 01NK]'s `θ` for the induced datum**, along a morphism `j : U(ψ') ⟶ U'`
with `j ≫ r' = r_{ℒ|_{f^{-1}(V)}, ψ'} ≫ i_V`: the pseudofunctoriality of the inverse image and the
chart identification of the twists of [Stacks, Tag 01NR]. -/
def sourceIso (P : GradedPowerMap A f) (t : Triple A P.L) (V : S.affineOpens)
    (j : ((P.affineDatum V.1).coveringOpen).toScheme ⟶ t.1.toScheme)
    (hj : j ≫ t.2.1 = (P.affineDatum V.1).glued ≫ (relativeProj A).chart V.1 V.2) (n : ℤ) :
    (Scheme.Modules.pullback j).obj ((Scheme.Modules.pullback t.2.1).obj
        ((GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra.piece n))
      ≅ (Scheme.Modules.pullback (P.affineDatum V.1).glued).obj
          (Stacks.AlgebraicGeometry.ProjChartGradedTheta.twistM (A.grading V.1) n) :=
  (Scheme.Modules.pullbackComp j t.2.1).app _
    ≪≫ (Scheme.Modules.pullbackCongr hj).app _
    ≪≫ (Scheme.Modules.pullbackComp (P.affineDatum V.1).glued
          ((relativeProj A).chart V.1 V.2)).symm.app _
    ≪≫ (Scheme.Modules.pullback (P.affineDatum V.1).glued).mapIso
          (Stacks.AlgebraicGeometry.Tag07ZGTwist.chartTwistIso A n V)

/-- **The target of `θ'` over the piece of `U'` over an affine open `V` of the base, read as the
target of [Stacks, Tag 01NK]'s `θ` for the induced datum**, along a morphism `j : U(ψ') ⟶ U'`
over `X`: the pseudofunctoriality of the inverse image and the comparison of the integer tensor
powers of [Stacks, Tag 01CU] with restriction to `f^{-1}(V)`. -/
def targetIso (P : GradedPowerMap A f) (t : Triple A P.L) (V : S.affineOpens)
    (j : ((P.affineDatum V.1).coveringOpen).toScheme ⟶ t.1.toScheme)
    (hj : j ≫ t.1.ι = ((P.affineDatum V.1).coveringOpen).ι ≫ (f ⁻¹ᵁ V.1).ι) (n : ℤ) :
    (Scheme.Modules.pullback j).obj ((laurentOn P.L t.1).piece n)
      ≅ (P.affineDatum V.1).laurentPiece n :=
  (Scheme.Modules.pullback j).mapIso
      ((Scheme.Modules.restrictFunctorIsoPullback t.1.ι).app (tensorPowerModule X P.L n))
    ≪≫ (Scheme.Modules.pullbackComp j t.1.ι).app _
    ≪≫ (Scheme.Modules.pullbackCongr hj).app _
    ≪≫ (Scheme.Modules.pullbackComp ((P.affineDatum V.1).coveringOpen).ι
          (f ⁻¹ᵁ V.1).ι).symm.app _
    ≪≫ (Scheme.Modules.pullback ((P.affineDatum V.1).coveringOpen).ι).mapIso
          (Stacks.AlgebraicGeometry.ProjChartIntPullbackMul.intPullIso (f ⁻¹ᵁ V.1).ι P.L n)
    ≪≫ ((Scheme.Modules.restrictFunctorIsoPullback
          ((P.affineDatum V.1).coveringOpen).ι).app _).symm

/-- **Property (3) of [Stacks, Tag 01O9]** for a triple `(U', r', θ')`, in full: for every affine
open `V` of the base, the restriction of `(U', r', θ')` over `V` agrees via `i_V` with the triple
`(U(ψ'), r_{ℒ|_{f^{-1}(V)}, ψ'}, θ)` of [Stacks, Tag 01NK] for the induced map
`ψ' : 𝒜(V) ⟶ Γ_*(f^{-1}(V), ℒ|_{f^{-1}(V)})`. That is: `U' ∩ f^{-1}(V) = U(ψ')`; for the inclusion
`j : U(ψ') ⟶ U'`, `j ≫ r' = r_{ℒ|_{f^{-1}(V)}, ψ'} ≫ i_V`; and, read through that equality, the
inverse image of `θ'` along `j` is [Stacks, Tag 01NK]'s `θ` in every degree `n ≥ 0`. -/
def IsClauseThree (P : GradedPowerMap A f) (t : Triple A P.L) : Prop :=
  ∀ V : S.affineOpens,
    (f ⁻¹ᵁ V.1).ι ''ᵁ (P.affineDatum V.1).coveringOpen = t.1 ⊓ f ⁻¹ᵁ V.1 ∧
      ∀ (j : ((P.affineDatum V.1).coveringOpen).toScheme ⟶ t.1.toScheme)
        (hjι : j ≫ t.1.ι = ((P.affineDatum V.1).coveringOpen).ι ≫ (f ⁻¹ᵁ V.1).ι),
        ∃ hj : j ≫ t.2.1 = (P.affineDatum V.1).glued ≫ (relativeProj A).chart V.1 V.2,
          ∀ n : ℕ,
            (sourceIso P t V j hj n).inv ≫ (Scheme.Modules.pullback j).map (t.2.2.app n)
                ≫ (targetIso P t V j hjι n).hom
              = (Stacks.AlgebraicGeometry.ProjChartGradedThetaBuild.theta (A.grading V.1)
                  (P.affineDatum V.1)).app n

/-- A triple **has properties (1), (2) and (3)** of [Stacks, Tag 01O9] for `ψ`. -/
def IsTriple (ψ : Twisting f (situationAlgebra A) 1 L) (t : Triple A L) : Prop :=
  IsClauseOne (toGradedPowerMap ψ) t ∧ IsClauseTwo ψ t ∧ IsClauseThree (toGradedPowerMap ψ) t

/-- **Property (3) forces the open**: a triple with property (3) has `U' = U(ψ)`, since the
preimages of the affine opens of the base cover `X`. -/
theorem coveringOpen_eq_of_isClauseThree {P : GradedPowerMap A f} {t : Triple A P.L}
    (h : IsClauseThree P t) : t.1 = P.coveringOpen := by
  ext x
  obtain ⟨V, hV, hxV, -⟩ := exists_isAffineOpen_mem_and_subset (Opens.mem_top (f.base x))
  have e := (h ⟨V, hV⟩).1.symm.trans (P.image_coveringOpen_affineDatum_eq hV)
  have h1 (U : X.Opens) : x ∈ U ↔ x ∈ U ⊓ f ⁻¹ᵁ V := ⟨fun h => ⟨h, hxV⟩, fun h => h.1⟩
  exact (h1 t.1).trans (e ▸ (h1 P.coveringOpen).symm)

/-- **Property (3) forces the open and the morphism**: a triple with property (3) is
`(U(ψ), r_{ℒ,ψ}, θ')` for some `θ'`. -/
theorem exists_eq_of_isClauseThree {P : GradedPowerMap A f} {t : Triple A P.L}
    (h : IsClauseThree P t) :
    ∃ θ' : GradedNonnegHom
        (Stacks.Conormal.gradedPullback (P.globalMorphism (relativeProj A))
          (GluedTwistAlgebra.twistDataOfGradedAlgebra A).algebra)
        (laurentOn P.L P.coveringOpen),
      t = ⟨P.coveringOpen, P.globalMorphism (relativeProj A), θ'⟩ := by
  obtain ⟨U', r', θ'⟩ := t
  obtain rfl : U' = P.coveringOpen := coveringOpen_eq_of_isClauseThree h
  obtain rfl : r' = P.globalMorphism (relativeProj A) :=
    P.eq_globalMorphism_of_clauseThree (relativeProj A) fun V =>
      ((h V).2 _ (P.affineDatumInclusion_ι V)).1
  exact ⟨θ', rfl⟩

/-! ### The canonical triple -/

/-- **The triple `(U(ψ), r_{ℒ,ψ}, θ)` of [Stacks, Tag 01O9]**, with `θ` in degrees `≥ 0`. -/
def canonical (P : GradedPowerMap A f) : Triple A P.L :=
  ⟨P.coveringOpen, P.globalMorphism (relativeProj A), GradedNonnegHom.ofHom P.theta⟩

/-- Two readings of an identity between a restricted section and a restricted section, over two
opens `W`, `B` with the same sections. -/
theorem restrict_map_iff {Y : Scheme.{u}} {U : Y.Opens} (M : Y.Modules)
    {O W B : U.toScheme.Opens} (hW : W ≤ O) (hB : B ≤ O) (hBW : B ≤ W) (hWB : W ≤ B) {Z : Y.Opens}
    (x : Γ(M.restrict U.ι, O)) (y : Γ(M, Z)) (h₁ : U.ι ''ᵁ W ≤ Z) (h₂ : U.ι ''ᵁ B ≤ Z) :
    (M.restrict U.ι).presheaf.map (homOfLE hW).op x = M.presheaf.map (homOfLE h₁).op y ↔
      (M.restrict U.ι).presheaf.map (homOfLE hB).op x = M.presheaf.map (homOfLE h₂).op y := by
  have key : ∀ {W B : U.toScheme.Opens} (hW : W ≤ O) (hB : B ≤ O) (hBW : B ≤ W)
      (h₁ : U.ι ''ᵁ W ≤ Z) (h₂ : U.ι ''ᵁ B ≤ Z),
      (M.restrict U.ι).presheaf.map (homOfLE hW).op x = M.presheaf.map (homOfLE h₁).op y →
        (M.restrict U.ι).presheaf.map (homOfLE hB).op x = M.presheaf.map (homOfLE h₂).op y := by
    intro W B hW hB hBW h₁ h₂ h
    have e := congrArg ((M.restrict U.ι).presheaf.map (homOfLE hBW).op) h
    refine (map_map (M.restrict U.ι) (homOfLE hW).op (homOfLE hBW).op _ x).symm.trans
      (e.trans ?_)
    exact map_map M (homOfLE h₁).op (U.ι.opensFunctor.map (homOfLE hBW)).op _ y
  exact ⟨key hW hB hBW h₁ h₂, key hB hW hWB h₂ h₁⟩

/-- Property (1) for a triple `(U(ψ), r_{ℒ,ψ}, θ')` is the commutativity of the square of the tag,
read over `r_{ℒ,ψ}^{-1}(π^{-1}(V)) = f^{-1}(V) ∩ U(ψ)`. -/
theorem isClauseOne_iff (P : GradedPowerMap A f)
    (θ' : GradedNonnegHom
      (Stacks.Conormal.gradedPullback (P.globalMorphism (relativeProj A))
        (GradedPowerMap.twD A).algebra)
      (laurentOn P.L P.coveringOpen)) :
    IsClauseOne P ⟨P.coveringOpen, P.globalMorphism (relativeProj A), θ'⟩ ↔
      ∀ (V : S.Opens) (d : ℕ) (a : Γ(A.piece (d : ℤ), V)),
        (P.powK d).presheaf.map (eqToHom (P.toBase_preimage_eq V)).op
            ((θ'.app d).val.app
              (op (P.globalMorphism (relativeProj A) ⁻¹ᵁ ((relativeProj A).toBase ⁻¹ᵁ V)))
              (pullbackUnit (P.globalMorphism (relativeProj A)).toLRSHom.toShHom
                ((GradedPowerMap.twD A).algebra.piece (d : ℤ))
                (op ((relativeProj A).toBase ⁻¹ᵁ V))
                (((GradedPowerMap.twD A).ψ d).app V a)))
          = (tensorPowerModule X P.L d).presheaf.map
              (homOfLE (P.coveringOpen.ι.image_preimage_le (f ⁻¹ᵁ V))).op
              ((powCompare P.L d).hom.app (f ⁻¹ᵁ V) (P.value d V a)) := by
  refine forall_congr' fun V => forall_congr' fun d => forall_congr' fun a => ?_
  rw [show (eqToHom (P.toBase_preimage_eq V)).op = (homOfLE (P.toBase_preimage_eq V).le).op from
    Subsingleton.elim _ _]
  exact restrict_map_iff (tensorPowerModule X P.L (d : ℤ)) _ _
    (le_inf (P.toBase_preimage_eq V).le fun _ hx => hx) (fun _ hx => hx.2) _ _ _ _

/-- `(U(ψ), r_{ℒ,ψ}, θ)` has property (1). -/
theorem isClauseOne_canonical (P : GradedPowerMap A f) : IsClauseOne P (canonical P) :=
  (isClauseOne_iff P (GradedNonnegHom.ofHom P.theta)).2 P.theta_clauseOne

/-- `(U(ψ), r_{ℒ,ψ}, θ)` has property (2). -/
theorem isClauseTwo_canonical (ψ : Twisting f (situationAlgebra A) 1 L) :
    IsClauseTwo ψ (canonical (toGradedPowerMap ψ)) :=
  fun hk W _ => clauseTwo ψ hk W

end Triple

end Stacks.AlgebraicGeometry.RelativeProjInvertibleMorphism

end
