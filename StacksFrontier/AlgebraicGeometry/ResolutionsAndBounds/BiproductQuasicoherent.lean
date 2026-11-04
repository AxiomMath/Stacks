module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Quasicoherent
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.CategoryTheory.Limits.Preserves.Shapes.Zero
public import Mathlib.CategoryTheory.Sites.Spaces
public import Mathlib.AlgebraicGeometry.Modules.Sheaf
public import StacksCore.Tactic.StacksAttribute

/-!
# Direct sums of quasi-coherent sheaves of modules

The direct sum of two quasi-coherent sheaves of modules on a topological space is
quasi-coherent.

## Main results

* `AlgebraicGeometry.directSum_isQuasicoherent`: the binary biproduct of two quasi-coherent
  sheaves of modules is quasi-coherent.
* `AlgebraicGeometry.directSum_isQuasicoherent_scheme`: the same statement for modules on a
  scheme.

## References

* [Stacks Project, Tag 01BF](https://stacks.math.columbia.edu/tag/01BF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open SheafOfModules

namespace AlgebraicGeometry

universe u v

variable {X : TopCat.{u}} (𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{u})

/-- Restricting to an open commutes with the direct sum. -/
private noncomputable def biprodOverIso (M N : SheafOfModules.{u} 𝒪)
    [HasBinaryBiproduct M N]
    (U : Opens X) [HasBinaryBiproduct (M.over U) (N.over U)] :
    (M ⊞ N).over U ≅ (M.over U) ⊞ (N.over U) := by
  let F : SheafOfModules.{u} 𝒪 ⥤ SheafOfModules.{u} (𝒪.over U) := SheafOfModules.overFunctor 𝒪 U
  have : PreservesColimitsOfSize.{0, 0} F :=
    (SheafOfModules.overPushforwardOverAdj (R := 𝒪) U).leftAdjoint_preservesColimits
  have : Functor.PreservesZeroMorphisms F := ⟨fun _ _ => by ext; rfl⟩
  have : PreservesBinaryBiproduct M N F := preservesBinaryBiproduct_of_preservesBinaryCoproduct F
  exact F.mapBiprod M N

/-- The biproduct of two colimit cokernel coforks is a colimit cokernel cofork. -/
private noncomputable def biprodCokernelIsColimit
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {X₁ Y₁ Z₁ X₂ Y₂ Z₂ : C}
    [HasBinaryBiproduct X₁ X₂] [HasBinaryBiproduct Y₁ Y₂] [HasBinaryBiproduct Z₁ Z₂]
    (f₁ : X₁ ⟶ Y₁) (p₁ : Y₁ ⟶ Z₁) (h₁ : f₁ ≫ p₁ = 0)
    (c₁ : IsColimit (CokernelCofork.ofπ p₁ h₁))
    (f₂ : X₂ ⟶ Y₂) (p₂ : Y₂ ⟶ Z₂) (h₂ : f₂ ≫ p₂ = 0)
    (c₂ : IsColimit (CokernelCofork.ofπ p₂ h₂))
    (hbig : biprod.map f₁ f₂ ≫ biprod.map p₁ p₂ = 0) :
    IsColimit (CokernelCofork.ofπ (biprod.map p₁ p₂) hbig) := by
  refine CokernelCofork.IsColimit.ofπ _ _
    (fun {W} g eqg =>
      biprod.desc
        (CokernelCofork.IsColimit.desc' c₁ (biprod.inl ≫ g)
          (by rw [← biprod.inl_map_assoc f₁ f₂, eqg, comp_zero])).1
        (CokernelCofork.IsColimit.desc' c₂ (biprod.inr ≫ g)
          (by rw [← biprod.inr_map_assoc f₁ f₂, eqg, comp_zero])).1)
    ?_ ?_
  · intro W g eqg
    apply biprod.hom_ext'
    · rw [biprod.inl_map_assoc, biprod.inl_desc]
      exact (CokernelCofork.IsColimit.desc' c₁ (biprod.inl ≫ g) _).2
    · rw [biprod.inr_map_assoc, biprod.inr_desc]
      exact (CokernelCofork.IsColimit.desc' c₂ (biprod.inr ≫ g) _).2
  · intro W g eqg m hm
    apply biprod.hom_ext'
    · rw [biprod.inl_desc]
      refine Cofork.IsColimit.hom_ext c₁ ?_
      have key : p₁ ≫ biprod.inl ≫ m = biprod.inl ≫ g := by
        rw [← biprod.inl_map_assoc p₁ p₂, hm]
      exact key.trans (CokernelCofork.IsColimit.desc' c₁ (biprod.inl ≫ g) _).2.symm
    · rw [biprod.inr_desc]
      refine Cofork.IsColimit.hom_ext c₂ ?_
      have key : p₂ ≫ biprod.inr ≫ m = biprod.inr ≫ g := by
        rw [← biprod.inr_map_assoc p₁ p₂, hm]
      exact key.trans (CokernelCofork.IsColimit.desc' c₂ (biprod.inr ≫ g) _).2.symm

/-- Replacing the middle object of a cokernel presentation by an isomorphic one again gives a
cokernel presentation. -/
private noncomputable def cokernelTransportMid
    {C : Type*} [Category C] [HasZeroMorphisms C]
    {X Y Yb Z : C} (e : Yb ≅ Y) (f : X ⟶ Y) (p : Y ⟶ Z) (h : f ≫ p = 0)
    (hc : IsColimit (CokernelCofork.ofπ p h)) :
    IsColimit (CokernelCofork.ofπ (e.hom ≫ p)
      (show (f ≫ e.inv) ≫ (e.hom ≫ p) = 0 by simp [Category.assoc, h])) := by
  exact Cofork.isColimitOfIsos _ hc _ (Iso.refl _) e.symm (Iso.refl _)

/-- The direct sum of a presentation of `A` and a presentation of `B` is a presentation of
`A ⊞ B`, with relations and generators indexed by the disjoint unions of the given index
types. -/
private noncomputable def biprodPresentation
    {C : Type v} [Category.{v, v} C] {J : GrothendieckTopology C}
    {R : Sheaf J RingCat.{u}}
    [HasSheafify J AddCommGrpCat.{u}] [J.WEqualsLocallyBijective AddCommGrpCat.{u}]
    [J.HasSheafCompose (forget₂ RingCat AddCommGrpCat)]
    {A B : SheafOfModules.{u} R} [HasBinaryBiproduct A B]
    (P : A.Presentation) (Q : B.Presentation) : (A ⊞ B).Presentation := by
  set fP : free P.relations.I ⟶ free P.generators.I :=
    P.relations.π ≫ kernel.ι _ with hfP
  set pP : free P.generators.I ⟶ A := P.generators.π with hpP
  set fQ : free Q.relations.I ⟶ free Q.generators.I :=
    Q.relations.π ≫ kernel.ι _ with hfQ
  set pQ : free Q.generators.I ⟶ B := Q.generators.π with hpQ
  have hfgP : fP ≫ pP = 0 := by rw [hfP, hpP, Category.assoc, kernel.condition, comp_zero]
  have hfgQ : fQ ≫ pQ = 0 := by rw [hfQ, hpQ, Category.assoc, kernel.condition, comp_zero]
  have cP : IsColimit (CokernelCofork.ofπ pP hfgP) := P.isColimit
  have cQ : IsColimit (CokernelCofork.ofπ pQ hfgQ) := Q.isColimit
  have hbig : biprod.map fP fQ ≫ biprod.map pP pQ = 0 := by
    apply biprod.hom_ext' <;> simp [reassoc_of% hfgP, reassoc_of% hfgQ]
  have cBig : IsColimit (CokernelCofork.ofπ (biprod.map pP pQ) hbig) :=
    biprodCokernelIsColimit fP pP hfgP cP fQ pQ hfgQ cQ hbig
  have eGen : ((free P.generators.I : SheafOfModules R) ⊞
      (free Q.generators.I : SheafOfModules R)) ≅
      (free (P.generators.I ⊕ Q.generators.I) : SheafOfModules R) :=
    biprod.isoCoprod _ _ ≪≫ freeSumIso _ _
  have eRel : ((free P.relations.I : SheafOfModules R) ⊞
      (free Q.relations.I : SheafOfModules R)) ≅
      (free (P.relations.I ⊕ Q.relations.I) : SheafOfModules R) :=
    biprod.isoCoprod _ _ ≪≫ freeSumIso _ _
  have cMid : IsColimit (CokernelCofork.ofπ (eGen.symm.hom ≫ biprod.map pP pQ)
      (show (biprod.map fP fQ ≫ eGen.symm.inv) ≫
        (eGen.symm.hom ≫ biprod.map pP pQ) = 0 by simp [Category.assoc, hbig])) :=
    cokernelTransportMid eGen.symm (biprod.map fP fQ) (biprod.map pP pQ) hbig cBig
  refine presentationOfIsCokernelFree
    (eRel.symm.hom ≫ (biprod.map fP fQ ≫ eGen.symm.inv))
    (eGen.symm.hom ≫ biprod.map pP pQ)
    (show (eRel.symm.hom ≫ (biprod.map fP fQ ≫ eGen.symm.inv)) ≫
      (eGen.symm.hom ≫ biprod.map pP pQ) = 0 by
      simp only [Category.assoc, Iso.inv_hom_id_assoc]
      rw [hbig, comp_zero]) ?_
  exact isCokernelEpiComp cMid eRel.symm.hom rfl

/-- Over an open on which both `M` and `N` are presented, the direct sum `M ⊞ N` is
quasi-coherent. -/
private theorem biprodOverIsQuasicoherent
    {X : TopCat.{u}} {𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (M N : SheafOfModules.{u} 𝒪) (U : Opens X)
    (P : (M.over U).Presentation) (Q : (N.over U).Presentation) :
    ((M ⊞ N).over U).IsQuasicoherent := by
  let : Abelian (SheafOfModules.{u} (𝒪.over U)) := SheafOfModules.instAbelian (𝒪.over U)
  let : HasBinaryBiproduct (M.over U) (N.over U) := inferInstance
  exact ((biprodPresentation.{u, u, u} P Q).ofIsIso
    (biprodOverIso 𝒪 M N U).inv).isQuasicoherent

/-- A presentation of `M` over an open `W` restricts to a presentation over any open of `W`. -/
private noncomputable def presentationRestrict
    {X : TopCat.{u}} {𝒪 : Sheaf (Opens.grothendieckTopology X) RingCat.{u}}
    (M : SheafOfModules.{u} 𝒪) (W : Opens X) (U : Over W)
    (P : (M.over W).Presentation) : (M.over U.left).Presentation := by
  have PU : ((M.over W).over U).Presentation := P.quasicoherentData.presentation U
  letI e := SheafOfModules.pushforwardPushforwardEquivalence (Over.iteratedSliceEquiv U)
      (S := (𝒪.over W).over U) (R := 𝒪.over U.left) (𝟙 _) (𝟙 _)
      (by ext : 2; exact 𝒪.1.map_id _) (by ext : 2; exact 𝒪.1.map_id _)
  exact (PU.map e.inverse (.refl _)).ofIsIso
    (e.fullyFaithfulFunctor.preimageIso
      (by exact e.counitIso.app ((M.over W).over U))).hom

/-- The direct sum of two quasi-coherent sheaves of modules is quasi-coherent. -/
instance directSum_isQuasicoherent (M N : SheafOfModules.{u} 𝒪)
    [M.IsQuasicoherent] [N.IsQuasicoherent] :
    (M ⊞ N).IsQuasicoherent := by
  let qM : M.QuasicoherentData := (IsQuasicoherent.nonempty_quasicoherentData (M := M)).some
  let qN : N.QuasicoherentData := (IsQuasicoherent.nonempty_quasicoherentData (M := N)).some
  let qM' := qM.shrink
  let qN' := qN.shrink
  have overStar_coversTop : ∀ (W : Opens X) {I : Type u} (Y : I → Opens X),
      (Opens.grothendieckTopology X).CoversTop Y →
      ((Opens.grothendieckTopology X).over W).CoversTop
        (fun i => (Over.star W).obj (Y i)) := by
    intro W I Y h Z
    rw [GrothendieckTopology.mem_over_iff]
    refine (Opens.grothendieckTopology X).superset_covering ?_ (h Z.left)
    intro T g hg
    rw [Sieve.mem_ofObjects_iff] at hg
    obtain ⟨i, ⟨φ⟩⟩ := hg
    change (Sieve.functorPushforward (Over.forget W)
      (Sieve.ofObjects (fun i => (Over.star W).obj (Y i)) Z)) g
    refine ⟨Over.mk (g ≫ Z.hom), Over.homMk g rfl, 𝟙 _, ?_, by simp⟩
    rw [Sieve.mem_ofObjects_iff]
    exact ⟨i, ⟨Over.homMk (prod.lift (g ≫ Z.hom) φ) (Subsingleton.elim _ _)⟩⟩
  let W : (i : qM'.I) × qN'.I → Opens X := fun k =>
    ((Over.star (qM'.X k.1)).obj (qN'.X k.2)).left
  have hcov : (Opens.grothendieckTopology X).CoversTop W :=
    qM'.coversTop.over (I' := fun _ => qN'.I)
      (Y := fun i j => (Over.star (qM'.X i)).obj (qN'.X j))
      (fun i => overStar_coversTop (qM'.X i) qN'.X qN'.coversTop)
  let : ∀ k : (i : qM'.I) × qN'.I,
      ((M ⊞ N).over (W k)).IsQuasicoherent := by
    rintro ⟨i, j⟩
    let U : Over (qM'.X i) := (Over.star (qM'.X i)).obj (qN'.X j)
    have PM : (M.over U.left).Presentation :=
      presentationRestrict M (qM'.X i) U (qM'.presentation i)
    have PN : (N.over U.left).Presentation :=
      presentationRestrict N (qN'.X j)
        (Over.mk (Limits.prod.snd : U.left ⟶ qN'.X j)) (qN'.presentation j)
    simpa [W, U] using biprodOverIsQuasicoherent M N U.left PM PN
  exact SheafOfModules.IsQuasicoherent.of_coversTop (M ⊞ N) W hcov

/-- The direct sum of two quasi-coherent modules on a scheme is quasi-coherent. -/
instance directSum_isQuasicoherent_scheme {X : Scheme.{u}} (M N : X.Modules)
    [M.IsQuasicoherent] [N.IsQuasicoherent] : (M ⊞ N).IsQuasicoherent :=
  directSum_isQuasicoherent X.ringCatSheaf M N

end AlgebraicGeometry
