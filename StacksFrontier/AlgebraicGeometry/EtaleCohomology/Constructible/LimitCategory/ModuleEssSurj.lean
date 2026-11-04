module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleCoveringsRefine
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.LimitCategory.ModuleFullness
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ConstructibleComplexes.ShriekBaseChange
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.SmallEtaleCoveringsRefine
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Essential surjectivity of the comparison for constructible sheaves of modules on a limit

Let `X = lim X_i` be the limit of a directed inverse system of quasi-compact and quasi-separated
schemes with affine transition morphisms and let `Λ` be a Noetherian ring. Every constructible
sheaf of `Λ`-modules on `X_étale` is the inverse image of a constructible sheaf of `Λ`-modules on
some `(X_i)_étale`. This is the essential surjectivity assertion of Stacks 09YU, clause (3), and
with the faithfulness and fullness assertions it is the whole of that clause.

The proof is the source's. By Stacks 095N a constructible sheaf is the cokernel of a map between
finite direct sums of sheaves `j_{U!}Λ` with `U` affine. Affine étale objects of `X` are base
changed from a stage (Stacks 01ZM, 07RP, in the form of Stacks 0EYL for objects), and extension
by zero commutes with base change, so both sums are inverse images of sums at a stage; the map
between them comes from a later stage by fullness, and the cokernel there is constructible and
has the given sheaf as its inverse image.

## Main results

* `AlgebraicGeometry.moduleShriekConstantMapIso` — `j_{U!}Λ` is invariant under isomorphism of
  `U`.
* `AlgebraicGeometry.smallEtaleStagesEssSurj_isConstructibleModuleSheaf` — **Tag 09YU, clause
  (3), the essential surjectivity assertion.**
* `AlgebraicGeometry.smallEtaleStagesColimit_isConstructibleModuleSheaf` — **Tag 09YU, clause
  (3).**
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

attribute [local instance 2000] Sheaf.instHasColimitsOfShape Sheaf.instHasFiniteCoproducts

namespace AlgebraicGeometry

attribute [local instance] SmallEtale.isRightAdjointPushforward_addCommGrpCat

variable (B : BigEtaleSite.{u}) (Λ : Type (u + 1)) [CommRing Λ]

/-- **`j_{U!}Λ` is invariant under isomorphism of `U`.** -/
def moduleShriekConstantMapIso (X : B.Scheme) {U U' : SmallEtale B X.obj X.property}
    (e : U ≅ U') :
    moduleShriekConstant.{u, u + 1, u + 1} B X Λ U ≅
      moduleShriekConstant.{u, u + 1, u + 1} B X Λ U' :=
  letI := SmallEtale.hasSheafify_moduleCat.{u, u + 1, u + 1} B X Λ
  moduleShriekConstantIsoCopower B X Λ U ≪≫
    (Sheaf.composeAndSheafify (SmallEtale.topology B X.1 X.property)
      (ModuleCat.copower (ModuleCat.of Λ (ULift.{max (u + 1) (u + 1)} Λ)))).mapIso
        ((Sheaf.sheafifiedUliftYoneda.{u + 1} (SmallEtale.topology B X.1 X.property)).mapIso e) ≪≫
    (moduleShriekConstantIsoCopower B X Λ U').symm

variable {I : Type u} [Preorder I] [Nonempty I] [IsDirected I (· ≤ ·)]
  (Dg : Iᵒᵖ ⥤ B.Scheme) (c : Cone (Dg ⋙ B.inclusion)) (hX : B.Contains c.pt)

/-- **Stacks 09YU, clause (3), the essential surjectivity assertion.** Let `X = lim X_i` be the
limit of a directed inverse system of quasi-compact and quasi-separated schemes with affine
transition morphisms and let `Λ` be a Noetherian ring. Every constructible sheaf of `Λ`-modules on
`X_étale` is isomorphic to the inverse image of a constructible sheaf of `Λ`-modules on some
`(X_i)_étale`.

A constructible sheaf is the cokernel of a map between finite direct sums of sheaves `j_{U!}Λ`
with `U` affine (Stacks 095N); the affine `U` are base changed from a stage (Stacks 0EYL for
objects, which is Stacks 01ZM and 07RP), extension by zero commutes with base change, and the map
comes from a later stage by the fullness assertion; its cokernel there is constructible and
pulls back to the given sheaf, inverse image being right exact. -/
@[stacks 09YU "clause (3), the essential surjectivity assertion",
  sga "4 IX 2.7.4" "partial, special case"]
theorem smallEtaleStagesEssSurj_isConstructibleModuleSheaf [IsNoetherianRing Λ] (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesEssSurj B (ModuleCat.{u + 1} Λ) Dg c hX
      (fun Y => IsConstructibleModuleSheaf B Y Λ) := by
  intro F hF
  have : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom ((Dg ⋙ B.inclusion).map e) := fun e => haff e
  have : ∀ p : Iᵒᵖ, CompactSpace ((Dg ⋙ B.inclusion).obj p) := fun p => hqc p.unop
  have : CompactSpace (B.obj c.pt hX).obj :=
    Scheme.compactSpace_of_isLimit (Dg ⋙ B.inclusion) c hc
  let i₀ : I := Classical.arbitrary I
  have : QuasiSeparatedSpace (B.obj c.pt hX).obj := by
    have := hqs i₀
    have : IsAffineHom (c.π.app (op i₀)) := isAffineHom_π_app (Dg ⋙ B.inclusion) c hc (op i₀)
    have : QuasiSeparatedSpace ((Dg ⋙ B.inclusion).obj (op i₀)) := hqs i₀
    exact quasiSeparatedSpace_of_quasiSeparated (c.π.app (op i₀))
  let Xs := B.obj c.pt hX
  obtain ⟨n, V, hV, p, hp⟩ :=
    exists_finite_epi_sigma_moduleShriekConstant_affine_of_isConstructibleModuleSheaf B Xs Λ F hF
  have hP0 := isConstructibleModuleSheaf_sigma_moduleShriekConstant.{u, u + 1} B Xs Λ V hV
  let Q : ObjectProperty (Sheaf (SmallEtale.topology B Xs.obj Xs.property)
      (ModuleCat.{u + 1} Λ)) := fun H => IsConstructibleModuleSheaf B Xs Λ H
  let _ : Q.IsWeakSerreClass :=
    SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1} B _ Λ
  have hK : IsConstructibleModuleSheaf B Xs Λ (kernel p) := Q.prop_kernel p hP0 hF
  obtain ⟨m, W, hW, q, hq⟩ :=
    exists_finite_epi_sigma_moduleShriekConstant_affine_of_isConstructibleModuleSheaf B Xs Λ
      (kernel p) hK
  let Z : ULift.{u} (Fin n ⊕ Fin m) → SmallEtale B c.pt hX := fun t => Sum.elim V W t.down
  have hZ : ∀ t, IsAffine (B.inclusion.obj (Z t).obj.left) := by
    rintro ⟨k | l⟩
    exacts [hV k, hW l]
  obtain ⟨i, -, Y, hYaff, hYiso⟩ :=
    exists_common_stage_smallEtale_baseChange_iso B Dg c hX hc haff i₀ Z hZ
  let YA := fun k : Fin n => Y ⟨Sum.inl k⟩
  let YC := fun l : Fin m => Y ⟨Sum.inr l⟩
  have hA := isConstructibleModuleSheaf_sigma_moduleShriekConstant.{u, u + 1} B (Dg.obj (op i)) Λ
    YA (fun k => hYaff _)
  have hC := isConstructibleModuleSheaf_sigma_moduleShriekConstant.{u, u + 1} B (Dg.obj (op i)) Λ
    YC (fun l => hYaff _)
  have : ∀ k : I, PreservesColimitsOfSize.{0, 0}
      (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX k) := fun k =>
    (smallEtaleSheafAdjunction B (ModuleCat.{u + 1} Λ)
      (coneStageHom B Dg c hX k)).leftAdjoint_preservesColimits
  let eY : ∀ t, (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).obj
      (moduleShriekConstant.{u, u + 1, u + 1} B (Dg.obj (op i)) Λ (Y t)) ≅
      moduleShriekConstant.{u, u + 1, u + 1} B Xs Λ (Z t) := fun t =>
    moduleShriekConstantSheafPullbackIso.{u, u + 1} B Λ (coneStageHom B Dg c hX i) (Y t) ≪≫
      moduleShriekConstantMapIso B Λ Xs (hYiso t).some
  let eA : (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).obj
      (∐ fun k => moduleShriekConstant.{u, u + 1, u + 1} B (Dg.obj (op i)) Λ (YA k)) ≅
      ∐ fun k => moduleShriekConstant.{u, u + 1, u + 1} B Xs Λ (V k) :=
    PreservesCoproduct.iso (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i) _ ≪≫
      Sigma.mapIso (fun k => eY ⟨Sum.inl k⟩)
  let eC : (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i).obj
      (∐ fun l => moduleShriekConstant.{u, u + 1, u + 1} B (Dg.obj (op i)) Λ (YC l)) ≅
      ∐ fun l => moduleShriekConstant.{u, u + 1, u + 1} B Xs Λ (W l) :=
    PreservesCoproduct.iso (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX i) _ ≪≫
      Sigma.mapIso (fun l => eY ⟨Sum.inr l⟩)
  let mm := eC.hom ≫ q ≫ kernel.ι p ≫ eA.inv
  obtain ⟨j, hij, b, hb⟩ := smallEtaleStagesFull_isConstructibleModuleSheaf B Λ Dg c hX hc haff hqc
    hqs i _ _ hC hA mm
  let Qj : ObjectProperty (Sheaf (SmallEtale.topology B (Dg.obj (op j)).obj
      (Dg.obj (op j)).property) (ModuleCat.{u + 1} Λ)) :=
    fun H => IsConstructibleModuleSheaf B (Dg.obj (op j)) Λ H
  let _ : Qj.IsWeakSerreClass :=
    SmallEtale.isWeakSerreClass_isConstructibleModuleSheaf.{u, u + 1, u + 1} B _ Λ
  refine ⟨j, cokernel b, Qj.prop_cokernel b (isConstructibleModuleSheaf_pullback B Λ _ _ hC)
    (isConstructibleModuleSheaf_pullback B Λ _ _ hA), ⟨?_⟩⟩
  have hPjb : (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX j).map b =
      (smallEtaleStageComparison B (ModuleCat.{u + 1} Λ) Dg c hX hij _).hom ≫ mm ≫
        (smallEtaleStageComparison B (ModuleCat.{u + 1} Λ) Dg c hX hij _).inv := by
    rw [← hb]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, Iso.hom_inv_id, Category.comp_id]
  have : ∀ {A A' : Sheaf (SmallEtale.topology B c.pt hX) (ModuleCat.{u + 1} Λ)} (f : A ⟶ A'),
      HasCokernel f := fun f => HasCokernels.has_colimit f
  exact PreservesCokernel.iso (smallEtaleStageProjection B (ModuleCat.{u + 1} Λ) Dg c hX j) b ≪≫
    cokernelIsoOfEq hPjb ≪≫ cokernelEpiComp _ _ ≪≫ cokernelCompIsIso _ _ ≪≫
    cokernelEpiComp eC.hom _ ≪≫ cokernelEpiComp q _ ≪≫ cokernelCompIsIso _ _ ≪≫
    (cokernelIsCokernel (kernel.ι p)).coconePointUniqueUpToIso
      (Abelian.epiIsCokernelOfKernel (Fork.ofι (kernel.ι p) (kernel.condition p))
        (kernelIsKernel p))

/-- **Stacks 09YU, clause (3).** Let `X = lim X_i` be the limit of a directed inverse system of
schemes with affine transition morphisms, each `X_i` quasi-compact and quasi-separated, and let `Λ`
be a Noetherian ring. The category of constructible sheaves of `Λ`-modules on `X_étale` is the
colimit of the categories of constructible sheaves of `Λ`-modules on the `(X_i)_étale`: the
comparison, built from the inverse images and the canonical comparisons of iterated inverse
images, is faithful, full and essentially surjective. For a directed index these three conditions
are exactly the assertion that the canonical functor from the filtered colimit of the categories
is an equivalence.

Nothing is assumed beyond the source's hypotheses: a nonempty directed index, a limit cone,
affine transition morphisms, and quasi-compact quasi-separated stages. -/
@[stacks 09YU "clause (3)"]
theorem smallEtaleStagesColimit_isConstructibleModuleSheaf [IsNoetherianRing Λ] (hc : IsLimit c)
    (haff : ∀ {p q : Iᵒᵖ} (e : p ⟶ q), IsAffineHom (B.inclusion.map (Dg.map e)))
    (hqc : ∀ p : I, CompactSpace (Dg.obj (op p)).obj)
    (hqs : ∀ p : I, QuasiSeparatedSpace (Dg.obj (op p)).obj) :
    SmallEtaleStagesColimit B (ModuleCat.{u + 1} Λ) Dg c hX
      (fun Y => IsConstructibleModuleSheaf B Y Λ) where
  faithful := smallEtaleStagesFaithful_isConstructibleModuleSheaf B Λ Dg c hX hc haff hqc hqs
  full := smallEtaleStagesFull_isConstructibleModuleSheaf B Λ Dg c hX hc haff hqc hqs
  essSurj := smallEtaleStagesEssSurj_isConstructibleModuleSheaf B Λ Dg c hX hc haff hqc hqs

end AlgebraicGeometry
