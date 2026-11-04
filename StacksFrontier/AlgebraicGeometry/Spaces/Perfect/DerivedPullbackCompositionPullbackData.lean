module

public import StacksFrontier.AlgebraicGeometry.Spaces.Morphisms.PseudoCoherent.DerivedPullbackTriangulated
public import StacksFrontier.AlgebraicGeometry.Spaces.Perfect.LimitDerivedHom.CanonicalSystem
public import StacksFrontier.CategoryTheory.PullbackData.LimitHomSystem

/-!
# A pseudofunctoriality datum of derived pullback as a pullback pseudofunctor datum

A `AlgebraicGeometry.Space.DerivedPullbackComposition` carries, for the derived pullback
`Lf^* : D(𝒪_Y) ⥤ D(𝒪_X)` along morphisms of algebraic spaces, the identifications
`Lg^* ⋙ Lf^* ≅ Lk^*` attached to the factorisations `f ≫ g = k`, the identification
`L(𝟙)^* ≅ 𝟭`, and their associativity and unit coherences. This is exactly a coherent
`CategoryTheory.PullbackData` on the category of algebraic spaces, with fibre `D(𝒪_X)` over `X`.
Under this translation, the system of derived homomorphism sets of a relative descent situation
(Stacks 0DKU) is the system of morphism sets of `CategoryTheory.PullbackData.LimitSystem`.

## Main definitions

* `AlgebraicGeometry.Space.DerivedPullbackComposition.toPullbackData`: the pullback pseudofunctor
  datum of a pseudofunctoriality datum of derived pullback.
* `AlgebraicGeometry.Space.RelativeDescentSituation.toLimitSystem`: the base changes of a relative
  descent situation, as a directed system over the chosen space with a cone.

## Main results

* `AlgebraicGeometry.Space.DerivedPullbackComposition.isCoherent_toPullbackData`: the datum is
  coherent.
* `AlgebraicGeometry.Space.DerivedPullbackComposition.factorHom_toPullbackData`: the map of
  morphism sets attached to a factorisation is the one of the pseudofunctoriality datum.
* `AlgebraicGeometry.Space.RelativeDescentSituation.homDescent_iff_isColim`: the descent of
  derived homomorphisms of a relative descent situation is the colimit statement for its system.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.Space

universe u v

attribute [-instance] Stacks.Cohomology.SiteModules.moduleSheavesAbelian
  Stacks.Cohomology.SiteModules.moduleSheavesGrothendieck

attribute [local instance 5000] SheafOfModules.instAbelian


variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

variable (B S hS) in
/-- The derived category of `𝒪`-modules on an algebraic space, in the spelling of the small étale
ringed topos that derived pullback is built on, as a family indexed by the algebraic spaces over
`S`. -/
abbrev derivedToposModules (X : AlgebraicSpaces B S hS) :=
  @DerivedCategory (SheafOfModules.{u} (ringedToposStructureRingSheaf B S hS X))
    _ _ (HasDerivedCategory.standard _)

namespace DerivedPullbackComposition

variable (P : DerivedPullbackComposition B S hS)

/-- **A pseudofunctoriality datum of derived pullback, as a pullback pseudofunctor datum** on the
category of algebraic spaces, with fibre `D(𝒪_X)` over `X`: the inverse image along `f` is `Lf^*`,
the unit law is the identification `L(𝟙)^* ≅ 𝟭` and the composition comparison is the inverse of
the identification `Lg^* ⋙ Lf^* ≅ L(f ≫ g)^*`. -/
def toPullbackData : PullbackData (AlgebraicSpaces B S hS) (derivedToposModules B S hS) where
  pull f := smallEtaleDerivedModulePullback B S hS f
  idIso X := P.idIso X
  compIso f g := (P.iso f g (f ≫ g) rfl).symm

/-- The inverse image of `P.toPullbackData` along `f` is the derived pullback `Lf^*`. -/
theorem toPullbackData_pull {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    P.toPullbackData.pull f = smallEtaleDerivedModulePullback B S hS f :=
  rfl

/-- The inverse image of `P.toPullbackData` along `f` is additive. -/
instance additive_toPullbackData_pull {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (P.toPullbackData.pull f).Additive :=
  inferInstanceAs (smallEtaleDerivedModulePullback B S hS f).Additive

/-- The inverse image of `P.toPullbackData` along `f` commutes with the shift by `ℤ`. -/
instance commShift_toPullbackData_pull {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (P.toPullbackData.pull f).CommShift ℤ :=
  inferInstanceAs ((smallEtaleDerivedModulePullback B S hS f).CommShift ℤ)

/-- The inverse image of `P.toPullbackData` along `f` is a triangulated functor. -/
instance isTriangulated_toPullbackData_pull {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y) :
    (P.toPullbackData.pull f).IsTriangulated :=
  inferInstanceAs (smallEtaleDerivedModulePullback B S hS f).IsTriangulated

/-- The comparison of the datum attached to a factorisation is the inverse of the identification
of the pseudofunctoriality datum. -/
theorem triangle_toPullbackData {X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y ⟶ Z}
    {k : X ⟶ Z} (h : f ≫ g = k) :
    P.toPullbackData.triangle h = (P.iso f g k h).symm := by
  subst h
  exact P.toPullbackData.triangle_rfl f g

/-- **The datum is coherent**: its unit and associativity laws are the coherences of the
pseudofunctoriality datum. -/
theorem isCoherent_toPullbackData : P.toPullbackData.IsCoherent where
  triangle_id {a b} g hk := by
    rw [triangle_toPullbackData, P.iso_id g hk]
    ext M
    rfl
  triangle_comp {a b c d f g p k q r} hk hq hr hkr := by
    rw [triangle_toPullbackData, triangle_toPullbackData, triangle_toPullbackData,
      triangle_toPullbackData]
    ext M
    have key := congrArg Iso.inv (P.iso_assoc f g p q k r hq hk hkr hr M)
    simp only [Iso.trans_inv, Iso.app_inv, Functor.mapIso_inv] at key
    show (P.iso k p r hkr).inv.app M ≫
        (P.iso f g k hk).inv.app ((smallEtaleDerivedModulePullback B S hS p).obj M) =
      (P.iso f q r hr).inv.app M ≫
        (smallEtaleDerivedModulePullback B S hS f).map ((P.iso g p q hq).inv.app M) ≫ 𝟙 _
    rw [Category.comp_id]
    exact key

/-- **The map of morphism sets attached to a factorisation** by the pullback pseudofunctor datum
is the one attached to it by the pseudofunctoriality datum. -/
theorem factorHom_toPullbackData {X Y Z : AlgebraicSpaces B S hS} {f : X ⟶ Y} {g : Y ⟶ Z}
    {k : X ⟶ Z} (h : f ≫ g = k)
    (K L : derivedToposModules B S hS Z)
    (φ : (smallEtaleDerivedModulePullback B S hS g).obj K ⟶
      (smallEtaleDerivedModulePullback B S hS g).obj L) :
    P.toPullbackData.factorHom h φ = P.factorHom f g k h K L φ := by
  have key := Functor.conjHom_symm (P.iso f g k h) φ
  have e : P.factorHom f g k h K L φ = ((P.iso f g k h).app K).inv ≫
      (smallEtaleDerivedModulePullback B S hS f).map φ ≫ ((P.iso f g k h).app L).hom :=
    Iso.homCongr_apply _ _ _
  rw [e, key]
  unfold PullbackData.factorHom
  rw [triangle_toPullbackData]
  rfl

end DerivedPullbackComposition

/-! ### The system of a relative descent situation -/

namespace RelativeDescentSituation

variable {hZ : B.Contains (⊤_ Scheme.{u})} {I : Type v} [Preorder I] [IsDirected I (· ≤ ·)]
  (D : RelativeDescentSituation B S hS hZ I)

/-- **The base changes of a relative descent situation, as a directed system over the chosen
space**: the stages are the base changes `Xᵢ` at the indices at or beyond the chosen one, with
their projections to `X₀` and their transition morphisms, and the cone is the base change `X` at
the limit with its projections. -/
def toLimitSystem : PullbackData.LimitSystem (A := AlgebraicSpaces B S hS) D.initialSource
    D.LaterIndex where
  stage := D.stageSource
  toBase := D.stageToInitial
  transition h := D.sourceTransition h
  transition_toBase h := D.sourceTransition_comp_stageToInitial h
  transition_comp h h' := D.sourceTransition_comp_sourceTransition h h'
  limit := D.limitSource
  limitToBase := D.limitToInitial
  proj := D.sourceProjection
  proj_toBase := D.sourceProjection_comp_stageToInitial
  proj_transition h := D.sourceProjection_comp_sourceTransition h

variable
  [∀ {X Y : AlgebraicSpaces B S hS} (f : X ⟶ Y),
    (smallEtaleModulePullbackOnHomotopy B S hS f).HasLeftDerivedFunctor
      (smallEtaleModuleQuasiIso B S hS Y)]
  (P : DerivedPullbackComposition B S hS)
  (K₀ L₀ : @DerivedCategory (Modules.{u, u} B S hS D.X₀ D.initial_isAlgebraicSpace)
    _ _ (HasDerivedCategory.standard _))

/-- The transition maps `PullbackData.LimitSystem.trans` of `D.toLimitSystem` are the transition
maps `D.homTransition` of the system of derived homomorphism sets. -/
theorem trans_toLimitSystem {i j : D.LaterIndex} (h : i ≤ j)
    (φ : (P.toPullbackData.pull (D.toLimitSystem.toBase i)).obj K₀ ⟶
      (P.toPullbackData.pull (D.toLimitSystem.toBase i)).obj L₀) :
    D.toLimitSystem.trans P.toPullbackData K₀ L₀ i j h φ = D.homTransition P K₀ L₀ h φ :=
  P.factorHom_toPullbackData (D.sourceTransition_comp_stageToInitial h) K₀ L₀ φ

/-- The comparison maps `PullbackData.LimitSystem.projHom` of `D.toLimitSystem` are the comparison
maps `D.homComparison` of the system of derived homomorphism sets. -/
theorem projHom_toLimitSystem (i : D.LaterIndex)
    (φ : (P.toPullbackData.pull (D.toLimitSystem.toBase i)).obj K₀ ⟶
      (P.toPullbackData.pull (D.toLimitSystem.toBase i)).obj L₀) :
    D.toLimitSystem.projHom P.toPullbackData K₀ L₀ i φ = D.homComparison P K₀ L₀ i φ :=
  P.factorHom_toPullbackData (D.sourceProjection_comp_stageToInitial i) K₀ L₀ φ

/-- **The descent of derived homomorphisms of a relative descent situation is the colimit
statement for its system**: `Hom_{D(𝒪_X)}(K, L)` is the filtered colimit of the
`Hom_{D(𝒪_{Xᵢ})}(Kᵢ, Lᵢ)` exactly when the comparison maps are jointly surjective and two
homomorphisms at a stage with the same image agree at a later stage. -/
theorem homDescent_iff_isColim :
    D.HomDescent P K₀ L₀ ↔ D.toLimitSystem.IsColim P.toPullbackData K₀ L₀ := by
  constructor
  · rintro ⟨hsurj, hinj⟩
    refine ⟨fun _ _ h φ => PullbackData.LimitSystem.projHom_trans (S := D.toLimitSystem)
      P.isCoherent_toPullbackData K₀ L₀ h φ, fun ψ => ?_, fun i φ φ' hφ => ?_⟩
    · obtain ⟨i, φ, hφ⟩ := hsurj ψ
      exact ⟨i, φ, (projHom_toLimitSystem D P K₀ L₀ i φ).trans hφ⟩
    · obtain ⟨j, h, hj⟩ := hinj i φ φ'
        ((projHom_toLimitSystem D P K₀ L₀ i φ).symm.trans
          (hφ.trans (projHom_toLimitSystem D P K₀ L₀ i φ')))
      exact ⟨j, h, (trans_toLimitSystem D P K₀ L₀ h φ).trans
        (hj.trans (trans_toLimitSystem D P K₀ L₀ h φ').symm)⟩
  · intro hc
    refine ⟨fun ψ => ?_, fun i φ φ' hφ => ?_⟩
    · obtain ⟨i, φ, hφ⟩ := hc.exists_stage ψ
      exact ⟨i, φ, (projHom_toLimitSystem D P K₀ L₀ i φ).symm.trans hφ⟩
    · obtain ⟨j, h, hj⟩ := hc.exists_trans_eq i φ φ'
        ((projHom_toLimitSystem D P K₀ L₀ i φ).trans
          (hφ.trans (projHom_toLimitSystem D P K₀ L₀ i φ').symm))
      exact ⟨j, h, (trans_toLimitSystem D P K₀ L₀ h φ).symm.trans
        (hj.trans (trans_toLimitSystem D P K₀ L₀ h φ'))⟩

end RelativeDescentSituation

end AlgebraicGeometry.Space

end
