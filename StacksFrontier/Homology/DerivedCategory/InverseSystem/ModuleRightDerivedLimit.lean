module

public import Mathlib
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Homology.DerivedCategory.DerivedLimits
public import StacksFrontier.Algebra.Homology.DerivedCategory.Products
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.MilnorShortExact
public import StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitFunctor

/-!
# The derived inverse limit of modules as a derived limit, and its Milnor sequence

An object of the derived category of compatible modules over an inverse system of rings
`A : ℕᵒᵖ ⥤ RingCat` determines an inverse system in the derived category of modules over `lim A`.
The right-derived inverse-limit functor of
`StacksFrontier.Homology.DerivedCategory.InverseSystem.ModuleInverseLimitFunctor` is a derived limit
of that system: its value sits in the canonical distinguished triangle whose other two vertices
are the product of the terms and whose middle morphism is `1 - shift`. Taking cohomology of that
triangle gives, in each degree, the Milnor short exact sequence
`0 ⟶ R¹ lim H^(p-1)(Kₙ) ⟶ H^p(R lim K) ⟶ lim H^p(Kₙ) ⟶ 0`.

## Main definitions

* `ModuleRightDerivedLimit.derivedModuleDiagram`: the inverse system in `D(lim A)` associated to
  an object of the derived category of compatible module systems.

## Main results

* `ModuleRightDerivedLimit.rightDerivedInverseLimit_isDerivedLimit`: every right-derived
  inverse-limit functor computes a derived limit, in the sense of the canonical product triangle.
* `ModuleRightDerivedLimit.inverseLimit_hasRightDerivedFunctor_and_homology_shortExact`: the
  cohomology of such a derived limit lies in the canonical short exact sequence built from
  `R¹ lim` and `lim` of the cohomology systems.

## Implementation notes

The derived module diagram is obtained by applying the limit-ring module-diagram functor to a
chosen representative complex and then evaluating at each index. The predicate
`CategoryTheory.Pretriangulated.IsDerivedLimit` records the whole distinguished triangle,
including the prescribed difference map on the product. Existence of the right-derived functor is
supplied by Tag 091D, whose acyclic replacements also give the degreewise short exact sequences
that model the triangle at complex level; exactness of countable products in `ModuleCat` and the
compatibility of `Q` with those products (Tag 07KC) transport the model into `D(lim A)`.

Homology in the category of compatible module systems is compared naturally with termwise
homology after restriction to the inverse-limit ring. These comparisons identify the difference
maps on the relevant products, after which the two maps of the short exact sequence are the
cokernel descent of the connecting morphism and the kernel lift of the next map in the long
exact cohomology sequence. The general form of the Milnor sequence for an abstract derived limit
is `DerivedCategory.isDerivedLimit_homology_shortExact`.

## References

* [Stacks Project, Tag 0CQD](https://stacks.math.columbia.edu/tag/0CQD)
* [Stacks Project, Tag 0CQE](https://stacks.math.columbia.edu/tag/0CQE)
* [Stacks Project, Tag 08TC](https://stacks.math.columbia.edu/tag/08TC)
-/
section

@[expose] public noncomputable section

open CategoryTheory Limits DerivedCategory

namespace ModuleRightDerivedLimit

attribute [local instance] HasDerivedCategory.standard

universe u v

attribute [local instance] ModuleInverseLimit.moduleDiagramFunctor_additive

/-- The inverse system in the derived category of modules over the inverse-limit ring obtained
by evaluating the limit-ring module diagram of a representative complex. -/
public noncomputable def derivedModuleDiagram (A : ℕᵒᵖ ⥤ RingCat.{u})
    (K : DerivedCategory (PresheafOfModules.{v} A)) :
    ℕᵒᵖ ⥤ DerivedCategory (ModuleCat.{v} (limit A : RingCat.{u})) where
  obj n := DerivedCategory.Q.obj
    ((((evaluation ℕᵒᵖ (ModuleCat.{v} (limit A : RingCat.{u}))).obj n).mapHomologicalComplex
      (ComplexShape.up ℤ)).obj
      (((ModuleInverseLimit.moduleDiagramFunctor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (DerivedCategory.Q.objPreimage K)))
  map {a b} f := DerivedCategory.Q.map
    ((NatTrans.mapHomologicalComplex
      ((evaluation ℕᵒᵖ (ModuleCat.{v} (limit A : RingCat.{u}))).map f)
      (ComplexShape.up ℤ)).app
      (((ModuleInverseLimit.moduleDiagramFunctor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        (DerivedCategory.Q.objPreimage K)))
  map_id X := by simp
  map_comp f g := by simp

/-- The `n`-th object of `derivedModuleDiagram A K` is the evaluation at `n` of a chosen
representative of `K`, viewed in the derived category of `limit A`-modules. -/
@[simp]
public theorem derivedModuleDiagram_obj (A : ℕᵒᵖ ⥤ RingCat.{u})
    (K : DerivedCategory (PresheafOfModules.{v} A)) (n : ℕᵒᵖ) :
    (derivedModuleDiagram A K).obj n = DerivedCategory.Q.obj
      ((((evaluation ℕᵒᵖ (ModuleCat.{v} (limit A : RingCat.{u}))).obj n).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj
        (((ModuleInverseLimit.moduleDiagramFunctor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (DerivedCategory.Q.objPreimage K))) := rfl

/-- The transition maps of `derivedModuleDiagram A K` are induced by the transition maps of a
chosen representative of `K`. -/
@[simp]
public theorem derivedModuleDiagram_map (A : ℕᵒᵖ ⥤ RingCat.{u})
    (K : DerivedCategory (PresheafOfModules.{v} A)) {a b : ℕᵒᵖ} (f : a ⟶ b) :
    (derivedModuleDiagram A K).map f = DerivedCategory.Q.map
      ((NatTrans.mapHomologicalComplex
        ((evaluation ℕᵒᵖ (ModuleCat.{v} (limit A : RingCat.{u}))).map f)
        (ComplexShape.up ℤ)).app
        (((ModuleInverseLimit.moduleDiagramFunctor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
          (DerivedCategory.Q.objPreimage K))) := rfl

end ModuleRightDerivedLimit
end

end

section

@[expose] public noncomputable section

open CategoryTheory Limits DerivedCategory Pretriangulated

namespace ModuleRightDerivedLimit

attribute [local instance] HasDerivedCategory.standard

universe u v

attribute [local instance] ModuleInverseLimit.moduleDiagramFunctor_additive

set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev productFunctor (_V : Type v)
    (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    PresheafOfModules.{v} A ⥤ ModuleCat.{v} (limit A : RingCat.{u}) where
  obj M := ∏ᶜ fun n : ℕ ↦ (ModuleInverseLimit.moduleDiagram A M).obj (Opposite.op n)
  map f := ModuleInverseLimit.productMap A f
  map_id M := by
    apply Pi.hom_ext
    intro n
    rw [ModuleInverseLimit.productMap, Pi.lift_comp_π]
    simp
  map_comp f g := by
    apply Pi.hom_ext
    intro n
    simp [ModuleInverseLimit.productMap]

set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev limitToProductNatTrans (V : Type v)
    (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    ModuleInverseLimit.inverseLimit A ⟶ productFunctor V A where
  app M := ModuleInverseLimit.inverseLimitToProduct A M
  naturality X Y f := by
    apply Pi.hom_ext
    intro n
    simp only [Category.assoc, ModuleInverseLimit.productMap, Pi.lift_comp_π,
      ModuleInverseLimit.inverseLimitToProduct]
    rw [Pi.lift_comp_π_assoc, ModuleInverseLimit.inverseLimit_map_π]

set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev differenceNatTrans (V : Type v)
    (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    productFunctor V A ⟶ productFunctor V A where
  app M := 𝟙 _ - Pi.lift fun n : ℕ ↦
    Pi.π (fun n : ℕ ↦ (ModuleInverseLimit.moduleDiagram A M).obj (Opposite.op n)) (n + 1) ≫
      (ModuleInverseLimit.moduleDiagram A M).map (homOfLE (Nat.le_succ n)).op
  naturality X Y f := by
    apply Pi.hom_ext
    intro n
    simp only [ModuleInverseLimit.productMap, Preadditive.comp_sub, Preadditive.sub_comp,
      Category.assoc, Pi.lift_comp_π, Category.comp_id, Category.id_comp]
    rw [Pi.lift_comp_π_assoc, Pi.lift_comp_π_assoc]
    congr 1
    simp only [Category.assoc]
    rw [(ModuleInverseLimit.moduleDiagramMap A f).naturality]

private noncomputable local instance productFunctor_additive (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    (productFunctor (ULift.{v} PUnit) A).Additive where
  map_add := by
    intro X Y f g
    change ModuleInverseLimit.productMap A (f + g) =
      ModuleInverseLimit.productMap A f + ModuleInverseLimit.productMap A g
    apply Pi.hom_ext
    intro n
    rw [ModuleInverseLimit.productMap, Pi.lift_comp_π, Preadditive.add_comp,
      ModuleInverseLimit.productMap, Pi.lift_comp_π, ModuleInverseLimit.productMap, Pi.lift_comp_π]
    rfl

set_option backward.isDefEq.respectTransparency false in
private lemma shortExact_complex (A : ℕᵒᵖ ⥤ RingCat.{u})
    (L : CochainComplex (PresheafOfModules.{v} A) ℤ)
    [hadd : (ModuleInverseLimit.inverseLimit A).Additive]
    (hzero : ∀ p : ℤ, ∃ h : ModuleInverseLimit.inverseLimitToProduct A (L.X p) ≫
        (differenceNatTrans (ULift.{v} PUnit) A).app (L.X p) = 0,
      (ShortComplex.mk (ModuleInverseLimit.inverseLimitToProduct A (L.X p))
        ((differenceNatTrans (ULift.{v} PUnit) A).app (L.X p)) h).ShortExact) :
    ∃ h : (NatTrans.mapHomologicalComplex
          (limitToProductNatTrans (ULift.{v} PUnit) A)
          (ComplexShape.up ℤ)).app L ≫
        (NatTrans.mapHomologicalComplex
          (differenceNatTrans (ULift.{v} PUnit) A)
          (ComplexShape.up ℤ)).app L = 0,
      (ShortComplex.mk
        ((NatTrans.mapHomologicalComplex
          (limitToProductNatTrans (ULift.{v} PUnit) A)
          (ComplexShape.up ℤ)).app L)
        ((NatTrans.mapHomologicalComplex
          (differenceNatTrans (ULift.{v} PUnit) A)
          (ComplexShape.up ℤ)).app L) h).ShortExact := by
  choose hz hs using hzero
  exact ⟨HomologicalComplex.hom_ext _ _ hz,
    HomologicalComplex.shortExact_of_degreewise_shortExact _ hs⟩

private noncomputable abbrev complexDiagram (A : ℕᵒᵖ ⥤ RingCat.{u})
    (L : CochainComplex (PresheafOfModules.{v} A) ℤ) :
    ℕᵒᵖ ⥤ CochainComplex (ModuleCat.{v} (limit A : RingCat.{u})) ℤ where
  obj n := (((evaluation ℕᵒᵖ (ModuleCat.{v} (limit A : RingCat.{u}))).obj n).mapHomologicalComplex
    (ComplexShape.up ℤ)).obj
      (((ModuleInverseLimit.moduleDiagramFunctor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        L)
  map {a b} f := (NatTrans.mapHomologicalComplex
    ((evaluation ℕᵒᵖ (ModuleCat.{v} (limit A : RingCat.{u}))).map f)
    (ComplexShape.up ℤ)).app
      (((ModuleInverseLimit.moduleDiagramFunctor A).mapHomologicalComplex (ComplexShape.up ℤ)).obj
        L)
  map_id X := by simp
  map_comp f g := by simp

set_option backward.isDefEq.respectTransparency false in
private noncomputable def productProjection (A : ℕᵒᵖ ⥤ RingCat.{u}) (n : ℕ) :
    productFunctor (ULift.{v} PUnit) A ⟶
      ModuleInverseLimit.moduleDiagramFunctor A ⋙
        (evaluation ℕᵒᵖ (ModuleCat.{v} (limit A : RingCat.{u}))).obj (Opposite.op n) where
  app M := Pi.π (fun n : ℕ => (ModuleInverseLimit.moduleDiagram A M).obj (Opposite.op n)) n
  naturality X Y f := by
    change ModuleInverseLimit.productMap A f ≫ Pi.π _ n = _
    rw [ModuleInverseLimit.productMap, Pi.lift_comp_π]
    rfl

set_option backward.isDefEq.respectTransparency false in
-- Elaborating the degreewise product cone requires comparing composed evaluation functors.
private noncomputable def productComplexIsLimit (A : ℕᵒᵖ ⥤ RingCat.{u})
    (L : CochainComplex (PresheafOfModules.{v} A) ℤ) :
    IsLimit (Fan.mk
      (((productFunctor (ULift.{v} PUnit) A).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)
      (fun n => (NatTrans.mapHomologicalComplex (productProjection A n)
        (ComplexShape.up ℤ)).app L)) := by
  let t := Fan.mk
      (((productFunctor (ULift.{v} PUnit) A).mapHomologicalComplex
        (ComplexShape.up ℤ)).obj L)
      (fun n => (NatTrans.mapHomologicalComplex (productProjection A n)
        (ComplexShape.up ℤ)).app L)
  let lift (s : Fan (fun n : ℕ =>
      ((ModuleInverseLimit.moduleDiagramFunctor A ⋙
        (evaluation ℕᵒᵖ (ModuleCat.{v} (limit A : RingCat.{u}))).obj (Opposite.op n)
        ).mapHomologicalComplex (ComplexShape.up ℤ)).obj L)) :
      s.pt ⟶ t.pt :=
    { f := fun i => by
        exact Pi.lift (fun n => (s.π.app ⟨n⟩).f i)
      comm' := fun i j hij => by
        apply Pi.hom_ext
        intro n
        dsimp only [t]
        change ((Pi.lift fun n => (s.π.app ⟨n⟩).f i) ≫
            ModuleInverseLimit.productMap A (L.d i j)) ≫ Pi.π _ n =
          (s.pt.d i j ≫ Pi.lift fun n => (s.π.app ⟨n⟩).f j) ≫ Pi.π _ n
        rw [Category.assoc, ModuleInverseLimit.productMap, Pi.lift_comp_π, ← Category.assoc,
          Pi.lift_comp_π, Category.assoc, Pi.lift_comp_π]
        simpa [ModuleInverseLimit.moduleDiagramFunctor, ModuleInverseLimit.moduleDiagramMap] using
          (s.π.app ⟨n⟩).comm i j }
  refine { lift := lift, fac := ?_, uniq := ?_ }
  · rintro s ⟨n⟩
    exact HomologicalComplex.hom_ext _ _ fun i => Pi.lift_comp_π _ _
  · intro s m hm
    refine HomologicalComplex.hom_ext _ _ fun i => Pi.hom_ext _ _ fun n => ?_
    rw [Pi.lift_comp_π]
    simpa [productProjection] using congrArg (fun f => f.f i) (hm ⟨n⟩)

set_option backward.isDefEq.respectTransparency false in
/-- A distinguished triangle `X ⟶ P ⟶ P ⟶ X⟦1⟧` whose second vertex is the vertex of a limit
fan over `fun n : ℕ ↦ F.obj (Opposite.op n)`, and whose middle map is the difference map in the
coordinates of that fan, exhibits any object isomorphic to `X` as a derived limit of `F`. -/
public lemma isDerivedLimit_of_fan
    {D : Type*} [Category D] [HasZeroObject D] [HasShift D ℤ] [Preadditive D]
    [∀ n : ℤ, (shiftFunctor D n).Additive] [Pretriangulated D]
    (F : ℕᵒᵖ ⥤ D) {X Y P : D} (e : Y ≅ X)
    (p : ∀ n : ℕ, P ⟶ F.obj (Opposite.op n))
    (hp : IsLimit (Fan.mk P p))
    (f : X ⟶ P) (g : P ⟶ P) (δ : P ⟶ X⟦(1 : ℤ)⟧)
    (hT : Triangle.mk f g δ ∈ distTriang D)
    (hg : ∀ n : ℕ, g ≫ p n = p n - p (n + 1) ≫
      F.map (homOfLE (Nat.le_succ n)).op) :
    ∃ _ : HasProduct fun n : ℕ => F.obj (Opposite.op n),
      Pretriangulated.IsDerivedLimit F Y := by
  let : HasProduct fun n : ℕ => F.obj (Opposite.op n) := ⟨_, hp⟩
  let a := hp.conePointUniqueUpToIso (productIsProduct _)
  have ha (n : ℕ) : a.hom ≫ Pi.π _ n = p n :=
    hp.conePointUniqueUpToIso_hom_comp (productIsProduct _) ⟨n⟩
  have hai (n : ℕ) : a.inv ≫ p n = Pi.π _ n := by
    rw [← ha n, ← Category.assoc, a.inv_hom_id, Category.id_comp]
  refine ⟨inferInstance, e.hom ≫ f ≫ a.hom, a.inv ≫ δ ≫ e.inv⟦(1 : ℤ)⟧', ?_⟩
  apply Pretriangulated.isomorphic_distinguished _ hT
  refine Triangle.isoMk _ _ e a.symm a.symm ?_ ?_ ?_
  · simp
  · apply Fan.IsLimit.hom_ext hp
    intro n
    dsimp only [Triangle.mk_mor₂, Iso.symm_hom]
    change (_ ≫ a.inv) ≫ p n = (a.inv ≫ g) ≫ p n
    rw [Category.assoc, hai, Pi.lift_comp_π, Category.assoc, hg,
      Preadditive.comp_sub, ← Category.assoc, hai, hai]
  · simp

set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev complexDiagramMap (A : ℕᵒᵖ ⥤ RingCat.{u})
    {K L : CochainComplex (PresheafOfModules.{v} A) ℤ} (f : K ⟶ L) :
    complexDiagram A K ⟶ complexDiagram A L where
  app n := (((ModuleInverseLimit.moduleDiagramFunctor A ⋙
    (evaluation ℕᵒᵖ (ModuleCat.{v} (limit A : RingCat.{u}))).obj n)
    ).mapHomologicalComplex (ComplexShape.up ℤ)).map f
  naturality _ _ g := HomologicalComplex.hom_ext _ _ fun p =>
    ((ModuleInverseLimit.moduleDiagramFunctor A).map (f.f p)).naturality g

/-- Restriction of scalars along a ring homomorphism preserves homology. -/
public lemma restrictScalars_preservesHomology {R S : Type*} [Ring R] [Ring S]
    (f : R →+* S) : (ModuleCat.restrictScalars.{v} f).PreservesHomology := by
  apply ((Functor.exact_tfae (ModuleCat.restrictScalars.{v} f)).out 2 3).mp
  intro T hT
  rw [ShortComplex.ShortExact.moduleCat_exact_iff_function_exact] at hT ⊢
  assumption

set_option backward.isDefEq.respectTransparency false in
private lemma complexDiagramMap_quasiIso (A : ℕᵒᵖ ⥤ RingCat.{u})
    {K L : CochainComplex (PresheafOfModules.{v} A) ℤ} (f : K ⟶ L)
    [QuasiIso f] (n : ℕᵒᵖ) : QuasiIso ((complexDiagramMap A f).app n) := by
  have := restrictScalars_preservesHomology.{v} (limit.π A n).hom
  let E := PresheafOfModules.evaluation.{v} A n
  let R := ModuleCat.restrictScalars.{v} (limit.π A n).hom
  change QuasiIso ((R.mapHomologicalComplex (ComplexShape.up ℤ)).map
    ((E.mapHomologicalComplex (ComplexShape.up ℤ)).map f))
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private noncomputable def derivedComplexDiagramIso (A : ℕᵒᵖ ⥤ RingCat.{u})
    {K L : CochainComplex (PresheafOfModules.{v} A) ℤ} (f : K ⟶ L)
    [QuasiIso f] : complexDiagram A K ⋙ Q ≅ complexDiagram A L ⋙ Q := by
  haveI (n : ℕᵒᵖ) : IsIso (Q.map ((complexDiagramMap A f).app n)) := by
    have := complexDiagramMap_quasiIso A f n
    infer_instance
  exact NatIso.ofComponents (fun n => asIso (Q.map ((complexDiagramMap A f).app n)))
    (fun g => by
      simp only [asIso_hom, Functor.comp_map, ← Q.map_comp]
      exact congrArg Q.map ((complexDiagramMap A f).naturality g))

private lemma moduleCat_hasExactProducts (R : Type*) [Ring R] :
    HasExactLimitsOfShape (Discrete ℕ) (ModuleCat.{v} R) := by
  have := (forget₂ (ModuleCat.{v} R) Ab.{v}).preservesFiniteColimits_of_preservesHomology
  exact HasExactLimitsOfShape.domain_of_functor (Discrete ℕ)
    (forget₂ (ModuleCat.{v} R) Ab.{v})

set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev complexProduct (A : ℕᵒᵖ ⥤ RingCat.{u})
    (L : CochainComplex (PresheafOfModules.{v} A) ℤ) :=
  ((productFunctor (ULift.{v} PUnit) A).mapHomologicalComplex (ComplexShape.up ℤ)).obj L

set_option backward.isDefEq.respectTransparency false in
private noncomputable abbrev complexProductProjection (A : ℕᵒᵖ ⥤ RingCat.{u})
    (L : CochainComplex (PresheafOfModules.{v} A) ℤ) (n : ℕ) :
    complexProduct A L ⟶ (complexDiagram A L).obj (Opposite.op n) :=
  (NatTrans.mapHomologicalComplex (productProjection A n) (ComplexShape.up ℤ)).app L

set_option backward.isDefEq.respectTransparency false in
private noncomputable def derivedProductComplexIsLimit (A : ℕᵒᵖ ⥤ RingCat.{u})
    (L : CochainComplex (PresheafOfModules.{v} A) ℤ) :
    IsLimit (Fan.mk (Q.obj (complexProduct A L))
      (fun n => Q.map (complexProductProjection A L n))) := by
  have := moduleCat_hasExactProducts.{v} (limit A : RingCat.{u})
  have := Stacks.DerivedProducts.preservesLimitsOfShape_Q
    (A := ModuleCat.{v} (limit A : RingCat.{u})) (I := ℕ)
  exact Fan.isLimitMapConeEquiv Q _ _
    (isLimitOfPreserves Q (productComplexIsLimit A L))

set_option backward.isDefEq.respectTransparency false in
private lemma difference_comp_projection (A : ℕᵒᵖ ⥤ RingCat.{u})
    (L : CochainComplex (PresheafOfModules.{v} A) ℤ) (n : ℕ) :
    (NatTrans.mapHomologicalComplex (differenceNatTrans (ULift.{v} PUnit) A)
      (ComplexShape.up ℤ)).app L ≫ complexProductProjection A L n =
    complexProductProjection A L n - complexProductProjection A L (n + 1) ≫
      (complexDiagram A L).map (homOfLE (Nat.le_succ n)).op := by
  apply HomologicalComplex.Hom.ext
  funext p
  let X (k : ℕ) := (ModuleInverseLimit.moduleDiagram A (L.X p)).obj (Opposite.op k)
  change (differenceNatTrans (ULift.{v} PUnit) A).app (L.X p) ≫ Pi.π X n =
    Pi.π X n - Pi.π X (n + 1) ≫
      (ModuleInverseLimit.moduleDiagram A (L.X p)).map (homOfLE (Nat.le_succ n)).op
  simp only [X, Preadditive.sub_comp, Category.id_comp, Pi.lift_comp_π]

set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 0CQD.** The right-derived inverse-limit functor for compatible modules over an
inverse system of rings is, on every object, a derived limit of the associated inverse system in
the derived category of modules over the inverse-limit ring. Equivalently, its value fits in the
canonical distinguished triangle
`R lim K ⟶ ∏ Kₙ ⟶ ∏ Kₙ ⟶ (R lim K)⟦1⟧`, whose middle map is `1 - shift`. -/
@[stacks 0CQD]
public theorem rightDerivedInverseLimit_isDerivedLimit
    (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    let B := limit A
    let F : PresheafOfModules.{v} A ⥤ ModuleCat.{v} B := ModuleInverseLimit.inverseLimit A
    ∀ (hF : F.Additive),
      letI := hF
      ∀ (RF : DerivedCategory (PresheafOfModules.{v} A) ⥤
            DerivedCategory (ModuleCat.{v} B))
          (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
            DerivedCategory.Qh ⋙ RF),
        RF.IsRightDerivedFunctor α
            (HomotopyCategory.quasiIso (PresheafOfModules.{v} A) (ComplexShape.up ℤ)) →
        ∀ K : DerivedCategory (PresheafOfModules.{v} A),
          ∃ _ : HasProduct fun n : ℕ => (derivedModuleDiagram A K).obj (Opposite.op n),
            Pretriangulated.IsDerivedLimit (derivedModuleDiagram A K) (RF.obj K) := by
  intro B F hF
  let := hF
  intro RF α hRF K
  obtain ⟨hF', RF', α', hRF', _, _, _, hSES, _, hrep, hcomp⟩ :=
    ModuleInverseLimit.inverseLimit_hasRightDerivedFunctor_and_computations A
  have := hRF
  have := hRF'
  let C := Q.objPreimage K
  obtain ⟨L, f, hf, hacyc⟩ := hrep C
  have := hf
  obtain ⟨hz, hs⟩ := shortExact_complex A L (fun p => hSES (L.X p) (hacyc p))
  let S := ShortComplex.mk
    ((NatTrans.mapHomologicalComplex (limitToProductNatTrans (ULift.{v} PUnit) A)
      (ComplexShape.up ℤ)).app L)
    ((NatTrans.mapHomologicalComplex (differenceNatTrans (ULift.{v} PUnit) A)
      (ComplexShape.up ℤ)).app L) hz
  let e₀ : RF.obj K ≅ Q.obj S.X₁ :=
    (Functor.rightDerivedUnique RF RF' α α'
      (HomotopyCategory.quasiIso (PresheafOfModules.{v} A) (ComplexShape.up ℤ))).app K ≪≫
    RF'.mapIso ((Q.objObjPreimageIso K).symm ≪≫ asIso (Q.map f)) ≪≫
    (hcomp L hacyc).some
  let e : derivedModuleDiagram A K ≅ complexDiagram A L ⋙ Q :=
    derivedComplexDiagramIso A f
  let q (n : ℕ) := Q.map (complexProductProjection A L n)
  have hq : IsLimit (Fan.mk (Q.obj (complexProduct A L)) q) :=
    derivedProductComplexIsLimit A L
  let p (n : ℕ) := q n ≫ (e.app (Opposite.op n)).inv
  let e' : Discrete.functor (fun n : ℕ => (derivedModuleDiagram A K).obj (Opposite.op n)) ≅
      Discrete.functor (fun n : ℕ => (complexDiagram A L ⋙ Q).obj (Opposite.op n)) :=
    Discrete.natIso (fun n => e.app (Opposite.op n.as))
  have hp : IsLimit (Fan.mk (Q.obj (complexProduct A L)) p) := by
    apply IsLimit.ofIsoLimit ((IsLimit.postcomposeInvEquiv e'
      (Fan.mk (Q.obj (complexProduct A L)) q)).symm hq)
    refine Cone.ext (Iso.refl _) ?_
    intro n
    simp [e', p, ← Iso.app_inv]
  apply isDerivedLimit_of_fan (derivedModuleDiagram A K) e₀ p hp
    (Q.map S.f) (Q.map S.g) (triangleOfSESδ hs) (triangleOfSES_distinguished hs)
  intro n
  have hd : Q.map S.g ≫ q n = q n - q (n + 1) ≫
      Q.map ((complexDiagram A L).map (homOfLE (Nat.le_succ n)).op) := by
    simpa only [q, Functor.comp_map, Functor.map_sub, Functor.map_comp] using
      congrArg Q.map (difference_comp_projection A L n)
  change Q.map S.g ≫ (q n ≫ e.inv.app (Opposite.op n)) =
    (q n ≫ e.inv.app (Opposite.op n)) -
      (q (n + 1) ≫ e.inv.app (Opposite.op (n + 1))) ≫
        (derivedModuleDiagram A K).map (homOfLE (Nat.le_succ n)).op
  have hn := e.inv.naturality (homOfLE (Nat.le_succ n)).op
  dsimp only [Functor.comp_map] at hn
  rw [← Category.assoc, hd, Preadditive.sub_comp, Category.assoc,
    hn, ← Category.assoc]

end ModuleRightDerivedLimit

end

end
section

@[expose] public noncomputable section

open CategoryTheory Limits DerivedCategory

namespace ModuleRightDerivedLimit

attribute [local instance] HasDerivedCategory.standard

universe u v

-- `restrictScalars_preservesHomology` is shared with the derived-limit triangle above; the
-- additivity of the limit-ring module diagram comes from `ModuleInverseLimitFunctor`.
attribute [local instance] ModuleInverseLimit.moduleDiagramFunctor_additive

private noncomputable local instance moduleEvaluation_preservesHomology
    (A : ℕᵒᵖ ⥤ RingCat.{u}) (n : ℕᵒᵖ) :
    (ModuleInverseLimit.moduleDiagramFunctor A ⋙
      (evaluation ℕᵒᵖ (ModuleCat.{v} (limit A : RingCat.{u}))).obj n).PreservesHomology := by
  let := restrictScalars_preservesHomology.{v} (limit.π A n).hom
  change (PresheafOfModules.evaluation A n ⋙
    ModuleCat.restrictScalars.{v} (limit.π A n).hom).PreservesHomology
  let := (ModuleCat.restrictScalars.{v}
    (limit.π A n).hom).preservesFiniteLimits_of_preservesHomology
  let := (ModuleCat.restrictScalars.{v}
    (limit.π A n).hom).preservesFiniteColimits_of_preservesHomology
  infer_instance

set_option backward.isDefEq.respectTransparency false in
private noncomputable def derivedModuleDiagramHomologyIso
    (A : ℕᵒᵖ ⥤ RingCat.{u}) (K : DerivedCategory (PresheafOfModules.{v} A)) (p : ℤ) :
    ModuleRightDerivedLimit.derivedModuleDiagram A K ⋙ homologyFunctor (ModuleCat.{v} (limit A :
      RingCat.{u})) p ≅
      ModuleInverseLimit.moduleDiagram A ((homologyFunctor (PresheafOfModules.{v} A) p).obj K) := by
  let L := Q.objPreimage K
  let G := ModuleInverseLimit.moduleDiagramFunctor A
  let ev := evaluation ℕᵒᵖ (ModuleCat.{v} (limit A : RingCat.{u}))
  let e : ModuleRightDerivedLimit.derivedModuleDiagram A K ⋙
      homologyFunctor (ModuleCat.{v} (limit A : RingCat.{u})) p ≅
      G.obj (L.homology p) := NatIso.ofComponents
    (fun n => (homologyFunctorFactors _ p).app _ ≪≫ (L.sc p).mapHomologyIso (G ⋙ ev.obj n))
    (by
      intro i j f
      dsimp
      rw [Category.assoc, homologyFunctorFactors_hom_naturality_assoc]
      congr 1
      change ShortComplex.homologyMap ((L.sc p).mapNatTrans (Functor.whiskerLeft G (ev.map f))) ≫
        ((L.sc p).mapHomologyIso (G ⋙ ev.obj j)).hom = _
      rw [ShortComplex.homologyMap_mapNatTrans]
      simp
      rfl)
  exact e ≪≫ G.mapIso
    (((homologyFunctorFactors _ p).app L).symm ≪≫
      (homologyFunctor _ p).mapIso (Q.objObjPreimageIso K))

private noncomputable def homologyOneIsoCokernel
    {C : Type*} [Category C] [Abelian C] [HasDerivedCategory C]
    (L : CochainComplex C ℤ) (h : L.d 1 2 = 0) :
    (homologyFunctor C 1).obj (Q.obj L) ≅ cokernel (L.d 0 1) := by
  let S := L.sc' 0 1 2
  have : IsIso S.homologyι := ShortComplex.isIso_homologyι S h
  exact (homologyFunctorFactors C 1).app L ≪≫
    L.homologyIsoSc' 0 1 2 (by simp) (by simp) ≪≫
    asIso S.homologyι ≪≫ S.opcyclesIsoCokernel

private noncomputable abbrev difference {C : Type*} [Category C] [Preadditive C]
    (E : ℕᵒᵖ ⥤ C) [HasProduct fun n : ℕ => E.obj (Opposite.op n)] :
    (∏ᶜ fun n : ℕ => E.obj (Opposite.op n)) ⟶ ∏ᶜ fun n : ℕ => E.obj (Opposite.op n) :=
  Pi.lift fun n : ℕ => Pi.π _ n - Pi.π _ (n + 1) ≫
    E.map (homOfLE (Nat.le_succ n)).op

set_option backward.isDefEq.respectTransparency false in
private lemma map_difference_comp
    {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    (G : C ⥤ D) [G.Additive] (E : ℕᵒᵖ ⥤ C) (N : ℕᵒᵖ ⥤ D)
    [HasProduct fun n : ℕ => E.obj (Opposite.op n)]
    [HasProduct fun n : ℕ => N.obj (Opposite.op n)]
    (η : E ⋙ G ⟶ N)
    (a : G.obj (∏ᶜ fun n : ℕ => E.obj (Opposite.op n)) ⟶
      ∏ᶜ fun n : ℕ => N.obj (Opposite.op n))
    (ha : ∀ n : ℕ, a ≫ Pi.π _ n = G.map (Pi.π _ n) ≫ η.app (Opposite.op n)) :
    G.map (difference E) ≫ a = a ≫ difference N := by
  apply Pi.hom_ext
  intro n
  simp only [Category.assoc, ha, difference, Pi.lift_comp_π, Preadditive.comp_sub]
  rw [← Category.assoc, ← G.map_comp, Pi.lift_comp_π, G.map_sub, G.map_comp,
    Preadditive.sub_comp, Category.assoc]
  have hn := η.naturality (homOfLE (Nat.le_succ n)).op
  dsimp only [Functor.comp_map] at hn
  rw [hn]
  simp only [← Category.assoc, ha]

set_option maxHeartbeats 3000000 in
-- The homology comparison involves several product and localization isomorphisms.
set_option backward.isDefEq.respectTransparency false in
/-- **Stacks 0CQE.** For a complex of compatible modules over an inverse system of rings, the
long exact cohomology sequence of its canonical derived-limit triangle breaks into short exact
sequences
`0 ⟶ R¹ lim H^(p-1)(Kₙ) ⟶ H^p(R lim K) ⟶ lim H^p(Kₙ) ⟶ 0`.

The displayed maps are the cokernel descent of the connecting morphism and the kernel lift of
the following morphism in the long exact sequence. -/
@[stacks 0CQE]
public theorem inverseLimit_hasRightDerivedFunctor_and_homology_shortExact
    (A : ℕᵒᵖ ⥤ RingCat.{u}) :
    let B := limit A
    let F : PresheafOfModules.{v} A ⥤ ModuleCat.{v} B := ModuleInverseLimit.inverseLimit A
    ∃ (hF : F.Additive),
      letI := hF
      ∃ (RF : DerivedCategory (PresheafOfModules.{v} A) ⥤
            DerivedCategory (ModuleCat.{v} B))
          (α : F.mapHomotopyCategory (ComplexShape.up ℤ) ⋙ DerivedCategory.Qh ⟶
            DerivedCategory.Qh ⋙ RF),
        RF.IsRightDerivedFunctor α
            (HomotopyCategory.quasiIso (PresheafOfModules.{v} A) (ComplexShape.up ℤ)) ∧
        ∀ K : DerivedCategory (PresheafOfModules.{v} A),
          ∃ _ : HasProduct fun n : ℕ ↦
              (ModuleRightDerivedLimit.derivedModuleDiagram A K).obj (Opposite.op n),
            let E := ModuleRightDerivedLimit.derivedModuleDiagram A K
            let P := ∏ᶜ fun n : ℕ ↦ E.obj (Opposite.op n)
            let d : P ⟶ P := Pi.lift fun n : ℕ ↦
              Pi.π (fun n : ℕ ↦ E.obj (Opposite.op n)) n -
                Pi.π (fun n : ℕ ↦ E.obj (Opposite.op n)) (n + 1) ≫
                  E.map (homOfLE (Nat.le_succ n)).op
            ∃ (a : RF.obj K ⟶ P) (b : P ⟶ (RF.obj K)⟦(1 : ℤ)⟧),
              Pretriangulated.Triangle.mk a d b ∈
                  distTriang (DerivedCategory (ModuleCat.{v} B)) ∧
              ∀ p : ℤ,
                let H : ℤ → PresheafOfModules.{v} A := fun q ↦
                  (DerivedCategory.homologyFunctor (PresheafOfModules.{v} A) q).obj K
                let EH : ℤ → (ℕᵒᵖ ⥤ ModuleCat.{v} B) := fun q ↦
                  E ⋙ DerivedCategory.homologyFunctor (ModuleCat.{v} B) q
                let MH : ℤ → (ℕᵒᵖ ⥤ ModuleCat.{v} B) := fun q ↦
                  ModuleInverseLimit.moduleDiagram A (H q)
                let HP : ℤ → ModuleCat.{v} B := fun q ↦
                  (DerivedCategory.homologyFunctor (ModuleCat.{v} B) q).obj P
                let PH : ℤ → ModuleCat.{v} B := fun q ↦
                  ∏ᶜ fun n : ℕ ↦ (MH q).obj (Opposite.op n)
                let δH : (q : ℤ) → (PH q ⟶ PH q) := fun q ↦ Pi.lift fun n : ℕ ↦
                  Pi.π (fun n : ℕ ↦ (MH q).obj (Opposite.op n)) n -
                    Pi.π (fun n : ℕ ↦ (MH q).obj (Opposite.op n)) (n + 1) ≫
                      (MH q).map (homOfLE (Nat.le_succ n)).op
                let R1lim := (DerivedCategory.homologyFunctor (ModuleCat.{v} B) 1).obj
                  (RF.obj ((DerivedCategory.singleFunctor (PresheafOfModules.{v} A) 0).obj
                    (H (p - 1))))
                let HpRlim :=
                  (DerivedCategory.homologyFunctor (ModuleCat.{v} B) p).obj (RF.obj K)
                let limHp := F.obj (H p)
                let T := Pretriangulated.Triangle.mk a d b
                let connecting : HP (p - 1) ⟶ HpRlim :=
                  (DerivedCategory.homologyFunctor (ModuleCat.{v} B) 0).homologySequenceδ
                    T (p - 1) p (by omega)
                ∃ (eHPrev : EH (p - 1) ≅ MH (p - 1)) (eHCurr : EH p ≅ MH p)
                    (ePrev : HP (p - 1) ≅ PH (p - 1)) (eCurr : HP p ≅ PH p),
                  (∀ n : ℕ, ePrev.hom ≫
                      Pi.π (fun n : ℕ ↦ (MH (p - 1)).obj (Opposite.op n)) n =
                    (DerivedCategory.homologyFunctor (ModuleCat.{v} B) (p - 1)).map
                        (Pi.π (fun n : ℕ ↦ E.obj (Opposite.op n)) n) ≫
                      eHPrev.hom.app (Opposite.op n)) ∧
                  (∀ n : ℕ, eCurr.hom ≫
                      Pi.π (fun n : ℕ ↦ (MH p).obj (Opposite.op n)) n =
                    (DerivedCategory.homologyFunctor (ModuleCat.{v} B) p).map
                        (Pi.π (fun n : ℕ ↦ E.obj (Opposite.op n)) n) ≫
                      eHCurr.hom.app (Opposite.op n)) ∧
                  (DerivedCategory.homologyFunctor (ModuleCat.{v} B) (p - 1)).map d ≫
                      ePrev.hom = ePrev.hom ≫ δH (p - 1) ∧
                  (DerivedCategory.homologyFunctor (ModuleCat.{v} B) p).map d ≫
                      eCurr.hom = eCurr.hom ≫ δH p ∧
                  ∃ (eR1 : R1lim ≅ cokernel (δH (p - 1)))
                    (eLim : limHp ≅ kernel (δH p))
                    (hConnecting : δH (p - 1) ≫ ePrev.inv ≫ connecting = 0)
                    (hKernel : (DerivedCategory.homologyFunctor (ModuleCat.{v} B) p).map a ≫
                      eCurr.hom ≫ δH p = 0),
                    (∀ n : ℕ, eLim.hom ≫ kernel.ι (δH p) ≫
                        Pi.π (fun n : ℕ ↦ (MH p).obj (Opposite.op n)) n =
                      limit.π (MH p) (Opposite.op n)) ∧
                    let i : R1lim ⟶ HpRlim := eR1.hom ≫
                      cokernel.desc (δH (p - 1)) (ePrev.inv ≫ connecting) hConnecting
                    let q : HpRlim ⟶ limHp :=
                      kernel.lift (δH p)
                        ((DerivedCategory.homologyFunctor (ModuleCat.{v} B) p).map a ≫
                          eCurr.hom)
                        hKernel ≫ eLim.inv
                    ∃ w : i ≫ q = 0, (ShortComplex.mk i q w).ShortExact := by
  intro B F
  obtain ⟨hF, RF, α, hRF, _, htwo, _⟩ :=
    ModuleInverseLimit.inverseLimit_hasRightDerivedFunctor_and_computations A
  refine ⟨hF, RF, α, hRF, fun K => ?_⟩
  obtain ⟨hprod, a, b, hT⟩ := rightDerivedInverseLimit_isDerivedLimit A hF RF α hRF K
  let := hprod
  have := moduleCat_hasExactProducts.{v} B
  have := Stacks.DerivedProducts.hasProductsOfShape_derivedCategory (A := ModuleCat.{v} B) (I := ℕ)
  refine ⟨inferInstance, a, b, hT, fun p => ?_⟩
  let E := ModuleRightDerivedLimit.derivedModuleDiagram A K
  let X : ℕ → DerivedCategory (ModuleCat.{v} B) := fun n => E.obj (Opposite.op n)
  let H (q : ℤ) := homologyFunctor (ModuleCat.{v} B) q
  let M (q : ℤ) := (homologyFunctor (PresheafOfModules.{v} A) q).obj K
  let MH (q : ℤ) := ModuleInverseLimit.moduleDiagram A (M q)
  let δH (q : ℤ) := difference (MH q)
  let eH (q : ℤ) : E ⋙ H q ≅ MH q := derivedModuleDiagramHomologyIso A K q
  have (q : ℤ) : IsIso (piComparison (H q) X) :=
    Stacks.DerivedProducts.isIso_piComparison_homologyFunctor X q
  let eP (q : ℤ) : (H q).obj (∏ᶜ X) ≅ ∏ᶜ fun n : ℕ => (MH q).obj (Opposite.op n) :=
    asIso (piComparison (H q) X) ≪≫ Pi.mapIso (fun n : ℕ => (eH q).app (Opposite.op n))
  have hP (q : ℤ) (n : ℕ) : (eP q).hom ≫ Pi.π _ n =
      (H q).map (Pi.π X n) ≫ (eH q).hom.app (Opposite.op n) := by simp [eP]
  have hd (q : ℤ) : (H q).map (difference E) ≫ (eP q).hom =
      (eP q).hom ≫ δH q := map_difference_comp (H q) E (MH q) (eH q).hom (eP q).hom (hP q)
  let T := Pretriangulated.Triangle.mk a (difference E) b
  let c := HomologySequence.δ T (p - 1) p
  have hc : δH (p - 1) ≫ (eP (p - 1)).inv ≫ c = 0 := by
    rw [← cancel_epi (eP (p - 1)).hom, ← Category.assoc, ← hd]
    simp only [Category.assoc, Iso.hom_inv_id_assoc, comp_zero]
    exact HomologySequence.comp_δ T hT (p - 1) p
  have hca : c ≫ (H p).map a = 0 := HomologySequence.δ_comp T hT (p - 1) p
  have ha : ((H p).map a ≫ (eP p).hom) ≫ δH p = 0 := by
    have had : a ≫ difference E = 0 := Pretriangulated.comp_distTriang_mor_zero₁₂ T hT
    rw [Category.assoc, ← hd, ← Category.assoc, ← Functor.map_comp, had, Functor.map_zero,
      zero_comp]
  obtain ⟨L, e₀, e₁, hL, hdL, ⟨eL⟩⟩ := htwo (M (p - 1))
  have hdL' : L.d 0 1 ≫ e₁.hom = e₀.hom ≫ δH (p - 1) := by
    rw [← cancel_epi e₀.inv, Iso.inv_hom_id_assoc, hdL]
    exact Pi.hom_ext _ _ fun n => by
      simp only [δH, difference, MH, Preadditive.sub_comp, Category.id_comp, Pi.lift_comp_π]
  let eR1 := (H 1).mapIso eL ≪≫
    homologyOneIsoCokernel L ((hL 2 (by omega) (by omega)).eq_of_tgt _ _) ≪≫
      cokernel.mapIso (L.d 0 1) (δH (p - 1)) e₀ e₁ hdL'
  let eLim : F.obj (M p) ≅ kernel (δH p) :=
    (inverseSystemLimitKernelForkIsLimit (MH p)).conePointUniqueUpToIso (limit.isLimit _)
  have heLim : eLim.hom ≫ kernel.ι (δH p) = Pi.lift fun n : ℕ => limit.π (MH p) (Opposite.op n) :=
    IsLimit.conePointUniqueUpToIso_hom_comp _ _ WalkingParallelPair.zero
  refine ⟨eH (p - 1), eH p, eP (p - 1), eP p, hP (p - 1), hP p,
    hd (p - 1), hd p, eR1, eLim, hc, ha,
    fun n => by rw [← Category.assoc, heLim, Pi.lift_comp_π], ?_⟩
  let i := cokernel.desc (δH (p - 1)) ((eP (p - 1)).inv ≫ c) hc
  let q₀ := kernel.lift (δH p) ((H p).map a ≫ (eP p).hom) ha
  let q := q₀ ≫ eLim.inv
  have hi : cokernel.π (δH (p - 1)) ≫ i = (eP (p - 1)).inv ≫ c := cokernel.π_desc _ _ _
  have hia : i ≫ (H p).map a = 0 := by
    rw [← cancel_epi (cokernel.π (δH (p - 1))), ← Category.assoc, hi]
    simp only [Category.assoc, hca, comp_zero]
  have hiq : i ≫ q = 0 := by
    apply (cancel_mono eLim.hom).mp
    apply (cancel_mono (kernel.ι (δH p))).mp
    simp only [q, Category.assoc, Iso.inv_hom_id_assoc, zero_comp]
    rw [kernel.lift_ι, ← Category.assoc, hia, zero_comp]
  have hprev : (ShortComplex.mk (δH (p - 1)) ((eP (p - 1)).inv ≫ c) hc).Exact := by
    apply ShortComplex.exact_of_iso _ (HomologySequence.exact₃ T hT (p - 1) p)
    exact ShortComplex.isoMk (eP (p - 1)) (eP (p - 1)) (Iso.refl _)
      (by simpa [T, H] using (hd (p - 1)).symm) (by simp [c])
  have hcurr : (ShortComplex.mk ((H p).map a ≫ (eP p).hom) (δH p) ha).Exact := by
    apply ShortComplex.exact_of_iso _ (HomologySequence.exact₂ T hT p)
    exact ShortComplex.isoMk (Iso.refl _) (eP p) (eP p)
      (by simp [T, H]; rfl) (by simpa [T, H] using (hd p).symm)
  have : Mono i := hprev.mono_cokernelDesc
  have : Epi q₀ := hcurr.epi_kernelLift
  have : Epi q := inferInstanceAs (Epi (q₀ ≫ eLim.inv))
  have hs : (ShortComplex.mk i q hiq).ShortExact := by
    refine { exact := ?_, mono_f := inferInstance, epi_g := inferInstance }
    let S := ShortComplex.mk i ((H p).map a) hia
    let φ : ShortComplex.mk c ((H p).map a) hca ⟶ S :=
      { τ₁ := (eP (p - 1)).hom ≫ cokernel.π (δH (p - 1))
        τ₂ := 𝟙 _
        τ₃ := 𝟙 _
        comm₁₂ := by simp [S, i]
        comm₂₃ := by simp [S] }
    have hS : S.Exact :=
      (ShortComplex.exact_iff_of_epi_of_isIso_of_mono φ).mp
        (HomologySequence.exact₁ T hT (p - 1) p)
    let ψ : ShortComplex.mk i q hiq ⟶ S :=
      { τ₁ := 𝟙 _
        τ₂ := 𝟙 _
        τ₃ := eLim.hom ≫ kernel.ι (δH p) ≫ (eP p).inv
        comm₁₂ := by simp [S]
        comm₂₃ := by simp [S, q, q₀] }
    exact (ShortComplex.exact_iff_of_epi_of_isIso_of_mono ψ).mpr hS
  have hw : (eR1.hom ≫ i) ≫ q = 0 := by rw [Category.assoc, hiq, comp_zero]
  refine ⟨hw, ShortComplex.shortExact_of_iso ?_ hs⟩
  exact ShortComplex.isoMk eR1.symm (Iso.refl _) (Iso.refl _) (by simp; rfl) (by simp; rfl)

end ModuleRightDerivedLimit

end

end
