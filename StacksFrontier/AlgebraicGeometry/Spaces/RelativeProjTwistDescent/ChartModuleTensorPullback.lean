module

public import StacksFrontier.AlgebraicGeometry.ModuleLimits.Invertible
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.PresentationDescentMonoidal
public import StacksFrontier.AlgebraicGeometry.Spaces.RelativeProjTwistDescent.ChartModuleTensorNaturality

/-!
# Descending a multiplication of quasi-coherent modules along a presentation

Let `X = U/R` be a presentation of an algebraic space and let `(M, τ)`, `(N, σ)`, `(K, κ)` be
quasi-coherent modules on the presenting scheme `U` with scheme transitions, so that they descend
to quasi-coherent `𝒪_X`-modules `D(M)`, `D(N)`, `D(K)` (Stacks 03M3).  A multiplication
`m : M ⊗ N ⟶ K` on the scheme `U` which is compatible with the transitions, read through the
comparison `g^*(M ⊗ N) ≅ g^*M ⊗ g^*N` of Stacks 03EL on schemes along the two projections, gives a
morphism `μ = (M ⊗ N)^a ≅ M^a ⊗ N^a ⟶ K^a` of the attached modules of Stacks 03DX (2) on the
atlas.  This file shows that `μ` carries the tensor product of the attached transitions to the
attached transition of `K`, provided the identification `(M ⊗ N)^a ≅ M^a ⊗ N^a` of Stacks 03DX
is compatible with inverse images along the two projections
(`AlgebraicGeometry.Space.RepresentedC3TensorCompat`), and descends `m` to a morphism
`D(M) ⊗ D(N) ⟶ D(K)`.  This is the descent of the multiplication of the twists in Stacks 084D.

## Main definitions

* `AlgebraicGeometry.Space.quasicoherentPullbackTensorIso`: Stacks 03EL for the inverse image
  along a morphism of the site, between quasi-coherent tensor products on schemes.
* `AlgebraicGeometry.Space.RepresentedC3TensorCompat`: the compatibility of the identification
  `(M ⊗ N)_{yoneda U} ≅ M_{yoneda U} ⊗ N_{yoneda U}` with inverse images along a morphism `g`
  of the site, through the identifications `g^*(M_{yoneda U}) ≅ (g^*M)_{yoneda V}` and Stacks
  03EL on both sides.
* `AlgebraicGeometry.Space.representedTensorChartMul`: the morphism
  `M^a ⊗ N^a ⟶ K^a` attached to a scheme multiplication `m : M ⊗ N ⟶ K`.
* `AlgebraicGeometry.Space.presentationDescendedMul`: **the descended multiplication**
  `D(M) ⊗ D(N) ⟶ D(K)`.

## Main results

* `AlgebraicGeometry.Space.transitionCommutes_representedTensorChartMul`: the attached
  multiplication carries the tensor product of the attached transitions to the attached
  transition of the target.
* `AlgebraicGeometry.Space.presentationDescendedMul_spec`: the inverse image along the atlas of
  the descended multiplication is the attached multiplication.

## Implementation notes

The computation is an abstract lemma at variables, instantiated once with every argument
explicit, as for `AlgebraicGeometry.Space.representedSchemeTransition_naturality`.

## References

* [Stacks Project, Tag 03DX](https://stacks.math.columbia.edu/tag/03DX)
* [Stacks Project, Tag 03EL](https://stacks.math.columbia.edu/tag/03EL)
* [Stacks Project, Tag 03M3](https://stacks.math.columbia.edu/tag/03M3)
* [Stacks Project, Tag 084D](https://stacks.math.columbia.edu/tag/084D)
-/

@[expose] public noncomputable section

open CategoryTheory MonoidalCategory

universe u

namespace AlgebraicGeometry.Space

attribute [local instance] modulesMonoidalCategory

section Abstract

variable {CU CV : Type*} [Category CU] [MonoidalCategory CU] [iCV : Category CV]
  [MonoidalCategory CV]
  (Pt Ps : CU ⥤ CV) {AM AN AK AMN : CU} (TU : AMN ≅ AM ⊗ AN) (Am : AMN ⟶ AK)
  (tA : Pt.obj (AM ⊗ AN) ≅ Pt.obj AM ⊗ Pt.obj AN)
  (sA : Ps.obj (AM ⊗ AN) ≅ Ps.obj AM ⊗ Ps.obj AN)
  {Mt Nt Kt MNt QT Ms Ns Ks MNs QS : CV}
  (cMt : Pt.obj AM ≅ Mt) (cNt : Pt.obj AN ≅ Nt) (cKt : Pt.obj AK ≅ Kt) (cMNt : Pt.obj AMN ≅ MNt)
  (cMs : Ps.obj AM ≅ Ms) (cNs : Ps.obj AN ≅ Ns) (cKs : Ps.obj AK ≅ Ks) (cMNs : Ps.obj AMN ≅ MNs)
  (et : MNt ⟶ QT) (es : MNs ⟶ QS) (es' : QS ⟶ MNs)
  (TRt : QT ≅ Mt ⊗ Nt) (TRs : QS ≅ Ms ⊗ Ns)
  (τ : Mt ⟶ Ms) (σ : Nt ⟶ Ns) (κ : Kt ⟶ Ks) (q : QT ⟶ QS) (mt : MNt ⟶ Kt) (ms : MNs ⟶ Ks)

/-- The inverse of the comparison along the source, read through the inverse of Stacks 03EL. -/
private theorem tensorReading_source_inv (hes : es ≫ es' = 𝟙 _)
    (hbs : Ps.map TU.hom ≫ sA.hom ≫ (cMs.hom ⊗ₘ cNs.hom) = cMNs.hom ≫ es ≫ TRs.hom) :
    sA.inv ≫ Ps.map TU.inv = (cMs.hom ⊗ₘ cNs.hom) ≫ TRs.inv ≫ es' ≫ cMNs.inv := by
  rw [← cancel_epi sA.hom, Iso.hom_inv_id_assoc, ← cancel_epi (Ps.map TU.hom),
    Iso.hom_inv_id_map, reassoc_of% hbs]
  simp [reassoc_of% hes]

/-- The comparison along the target, solved for Stacks 03EL. -/
private theorem tensorReading_target
    (hbt : Pt.map TU.hom ≫ tA.hom ≫ (cMt.hom ⊗ₘ cNt.hom) = cMNt.hom ≫ et ≫ TRt.hom) :
    tA.hom ≫ (cMt.hom ⊗ₘ cNt.hom) = Pt.map TU.inv ≫ cMNt.hom ≫ et ≫ TRt.hom := by
  rw [← hbt, Iso.inv_hom_id_map_assoc]

omit [MonoidalCategory CU] [MonoidalCategory CV] in
/-- Naturality of the chart identification along the source, solved for its inverse. -/
private theorem tensorReading_source_naturality
    (ns : Ps.map Am ≫ cKs.hom = cMNs.hom ≫ ms) :
    cMNs.inv ≫ Ps.map Am = ms ≫ cKs.inv := by
  rw [Iso.inv_comp_eq, ← reassoc_of% ns, Iso.hom_inv_id, Category.comp_id]

/-- Naturality of the tensor identification, solved for the tensor product of the
transitions. -/
private theorem tensorReading_tensor (hT : q ≫ TRs.hom = TRt.hom ≫ (τ ⊗ₘ σ)) :
    TRt.hom ≫ (τ ⊗ₘ σ) ≫ TRs.inv = q := by
  rw [← reassoc_of% hT, Iso.hom_inv_id, Category.comp_id]

omit [MonoidalCategory CU] [MonoidalCategory CV] in
/-- An equation, unchanged: it fixes the spelling of a hypothesis of
`AlgebraicGeometry.Space.transition_tensor_of_readings` in its own declaration. -/
private theorem tensorReading_target_naturality (nt : Pt.map Am ≫ cKt.hom = cMNt.hom ≫ mt) :
    Pt.map Am ≫ cKt.hom = cMNt.hom ≫ mt :=
  nt

omit [MonoidalCategory CV] in
/-- An equation, unchanged: it fixes the spelling of a hypothesis of
`AlgebraicGeometry.Space.transition_tensor_of_readings` in its own declaration. -/
private theorem tensorReading_mul (hm : et ≫ q ≫ es' ≫ ms = mt ≫ κ) :
    et ≫ q ≫ es' ≫ ms = mt ≫ κ :=
  hm

/-- The abstract shape of
`AlgebraicGeometry.Space.transitionCommutes_representedTensorChartMul`, at variables.  The three
morphisms of the conclusion are named by equations, so that an instance meets the spellings of its
goal argument by argument. -/
private theorem transition_tensor_of_readings
    (h1 : sA.inv ≫ Ps.map TU.inv = (cMs.hom ⊗ₘ cNs.hom) ≫ TRs.inv ≫ es' ≫ cMNs.inv)
    (ht : tA.hom ≫ (cMt.hom ⊗ₘ cNt.hom) = Pt.map TU.inv ≫ cMNt.hom ≫ et ≫ TRt.hom)
    (ns' : cMNs.inv ≫ Ps.map Am = ms ≫ cKs.inv)
    (hT' : TRt.hom ≫ (τ ⊗ₘ σ) ≫ TRs.inv = q)
    (nt : Pt.map Am ≫ cKt.hom = cMNt.hom ≫ mt)
    (hm : et ≫ q ≫ es' ≫ ms = mt ≫ κ)
    (α : Pt.obj (AM ⊗ AN) ⟶ Ps.obj (AM ⊗ AN))
    (hα : α = tA.hom ≫ ((cMt.hom ≫ τ ≫ cMs.inv) ⊗ₘ (cNt.hom ≫ σ ≫ cNs.inv)) ≫ sA.inv)
    (β : Pt.obj AK ⟶ Ps.obj AK) (hβ : β = cKt.hom ≫ κ ≫ cKs.inv)
    (f : AM ⊗ AN ⟶ AK) (hf : f = TU.inv ≫ Am) :
    α ≫ Ps.map f = Pt.map f ≫ β := by
  subst hα hβ hf
  calc (tA.hom ≫ ((cMt.hom ≫ τ ≫ cMs.inv) ⊗ₘ (cNt.hom ≫ σ ≫ cNs.inv)) ≫ sA.inv) ≫
        Ps.map (TU.inv ≫ Am)
      = tA.hom ≫ (((cMt.hom ≫ τ ≫ cMs.inv) ⊗ₘ (cNt.hom ≫ σ ≫ cNs.inv)) ≫
          (cMs.hom ⊗ₘ cNs.hom)) ≫ TRs.inv ≫ es' ≫ (cMNs.inv ≫ Ps.map Am) := by
        rw [Ps.map_comp]
        simp only [Category.assoc]
        rw [reassoc_of% h1]
    _ = (tA.hom ≫ (cMt.hom ⊗ₘ cNt.hom)) ≫ (τ ⊗ₘ σ) ≫ TRs.inv ≫ es' ≫ ms ≫ cKs.inv := by
        rw [ns']
        simp only [tensorHom_comp_tensorHom, tensorHom_comp_tensorHom_assoc, Category.assoc,
          Iso.inv_hom_id, Category.comp_id]
    _ = Pt.map TU.inv ≫ cMNt.hom ≫ et ≫ (TRt.hom ≫ (τ ⊗ₘ σ) ≫ TRs.inv) ≫ es' ≫ ms ≫
          cKs.inv := by
        rw [ht]
        simp only [Category.assoc]
    _ = Pt.map TU.inv ≫ cMNt.hom ≫ (et ≫ q ≫ es' ≫ ms) ≫ cKs.inv := by
        rw [hT']
        simp only [Category.assoc]
    _ = Pt.map (TU.inv ≫ Am) ≫ cKt.hom ≫ κ ≫ cKs.inv := by
        rw [hm, Pt.map_comp]
        simp only [Category.assoc]
        rw [reassoc_of% nt]

end Abstract

/-- A functor carries an equation `e⁻¹ ≫ a ≫ k = q ≫ e'⁻¹ ≫ b` to the equation of the images
used in `AlgebraicGeometry.Space.transitionCommutes_representedTensorChartMul`. -/
private theorem map_comp_eq_of_inv_comp_eq {E D : Type*} [Category E] [Category D] (G : E ⥤ D)
    {MNt QT MNs QS Kt Ks : E} (et : MNt ≅ QT) (es : MNs ≅ QS) (q : QT ⟶ QS) (mt : MNt ⟶ Kt)
    (ms : MNs ⟶ Ks) (κ : Kt ⟶ Ks) (hm : et.inv ≫ mt ≫ κ = q ≫ es.inv ≫ ms) :
    G.map et.hom ≫ G.map q ≫ G.map es.inv ≫ G.map ms = G.map mt ≫ G.map κ := by
  rw [← G.map_comp, ← G.map_comp, ← G.map_comp, ← G.map_comp, ← hm, Iso.hom_inv_id_assoc]

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **Stacks 03EL for the inverse image along a morphism of the site**: for a morphism
`g : V ⟶ U` of the big fppf site and quasi-coherent modules `M`, `N` on the scheme underlying
`U`, the comparison `g^*(M ⊗ N) ≅ g^*M ⊗ g^*N` of the scheme morphism underlying `g`
(`Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso`), as an isomorphism of quasi-coherent
modules. -/
def quasicoherentPullbackTensorIso {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    quasicoherentPullbackObj B S hS g (quasicoherentTensorObj B S hS U M N) ≅
      quasicoherentTensorObj B S hS V (quasicoherentPullbackObj B S hS g M)
        (quasicoherentPullbackObj B S hS g N) :=
  ObjectProperty.isoMk _
    (Stacks.AlgebraicGeometry.ModuleLimits.pullbackTensorIso
      ((BigFppfOver.toScheme B S hS).map g) M.obj N.obj)

/-- **The identification of Stacks 03DX (2) of the module attached to a tensor product is
compatible with inverse images.**  For a morphism `g : V ⟶ U` of the big fppf site and
quasi-coherent modules `M`, `N` on the scheme underlying `U`, the square

`g^*((M ⊗ N)_{yoneda U}) ≅ g^*(M_{yoneda U} ⊗ N_{yoneda U}) ≅ g^*M_{yoneda U} ⊗ g^*N_{yoneda U}`
`≅ (g^*M)_{yoneda V} ⊗ (g^*N)_{yoneda V}`

and

`g^*((M ⊗ N)_{yoneda U}) ≅ (g^*(M ⊗ N))_{yoneda V} ≅ (g^*M ⊗ g^*N)_{yoneda V}`
`≅ (g^*M)_{yoneda V} ⊗ (g^*N)_{yoneda V}`

commutes; the first uses `AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso` on
`U` and Stacks 03EL for the morphism of algebraic spaces, the second the identification
`AlgebraicGeometry.Space.modulePullbackRepresentedQuasicoherentIso`, Stacks 03EL on schemes
(`AlgebraicGeometry.Space.quasicoherentPullbackTensorIso`) and
`AlgebraicGeometry.Space.representedQuasicoherentSchemeTensorIso` on `V`. -/
def RepresentedC3TensorCompat {V U : BigFppfOver B S hS} (g : V ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) : Prop :=
  (modulePullback B S hS (representedSpaceMap B S hS g)).map
      (representedQuasicoherentSchemeTensorIso B S hS U M N).hom ≫
    (modulePullbackTensorIso B S hS (representedSpaceMap B S hS g)
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj).hom ≫
    ((modulePullbackRepresentedQuasicoherentIso B S hS g M).hom ⊗ₘ
      (modulePullbackRepresentedQuasicoherentIso B S hS g N).hom) =
  (modulePullbackRepresentedQuasicoherentIso B S hS g (quasicoherentTensorObj B S hS U M N)).hom ≫
    ((representedQuasicoherentSchemeEquivalence B S hS V).functor.map
      (quasicoherentPullbackTensorIso B S hS g M N).hom).hom ≫
    (representedQuasicoherentSchemeTensorIso B S hS V (quasicoherentPullbackObj B S hS g M)
      (quasicoherentPullbackObj B S hS g N)).hom

/-- The morphism `M^a ⊗ N^a ⟶ K^a` of the modules attached by Stacks 03DX (2) to quasi-coherent
modules on the scheme underlying `U`, attached to a morphism `m : M ⊗ N ⟶ K`: the inverse of the
identification `(M ⊗ N)^a ≅ M^a ⊗ N^a` followed by `m^a`. -/
def representedTensorChartMul {U : BigFppfOver B S hS}
    {M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (m : quasicoherentTensorObj B S hS U M N ⟶ K) :
    MonoidalCategoryStruct.tensorObj (C := Modules.{u, u} B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
        ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj ⟶
      ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj K).obj :=
  (representedQuasicoherentSchemeTensorIso B S hS U M N).inv ≫
    ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map m).hom

/-- The image under Stacks 03DX (2) of an equation `e⁻¹ ≫ t^*m ≫ κ = (τ ⊗ σ) ≫ e'⁻¹ ≫ s^*m` of
morphisms of quasi-coherent modules, written with the underlying morphisms of the attached
modules. -/
private theorem representedQuasicoherentSchemeEquivalence_map_comp_eq {R U : BigFppfOver B S hS}
    (t s : R ⟶ U)
    {M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (τ : quasicoherentPullbackObj B S hS t M ⟶ quasicoherentPullbackObj B S hS s M)
    (σ : quasicoherentPullbackObj B S hS t N ⟶ quasicoherentPullbackObj B S hS s N)
    (κ : quasicoherentPullbackObj B S hS t K ⟶ quasicoherentPullbackObj B S hS s K)
    (m : quasicoherentTensorObj B S hS U M N ⟶ K)
    (hm : (quasicoherentPullbackTensorIso B S hS t M N).inv ≫ quasicoherentPullbackMap B S hS t m ≫
        κ =
      quasicoherentTensorHom B S hS R τ σ ≫ (quasicoherentPullbackTensorIso B S hS s M N).inv ≫
        quasicoherentPullbackMap B S hS s m) :
    ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
        (quasicoherentPullbackTensorIso B S hS t M N).hom).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
        (quasicoherentTensorHom B S hS R τ σ)).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
        (quasicoherentPullbackTensorIso B S hS s M N).inv).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
        (quasicoherentPullbackMap B S hS s m)).hom =
    ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
        (quasicoherentPullbackMap B S hS t m)).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map κ).hom :=
  congrArg (fun x => x.hom)
    (map_comp_eq_of_inv_comp_eq (representedQuasicoherentSchemeEquivalence B S hS R).functor
      (quasicoherentPullbackTensorIso B S hS t M N) (quasicoherentPullbackTensorIso B S hS s M N)
      (quasicoherentTensorHom B S hS R τ σ) (quasicoherentPullbackMap B S hS t m)
      (quasicoherentPullbackMap B S hS s m) κ hm)

/-- The underlying morphisms of the attached isomorphism of Stacks 03DX (2) of the comparison of
Stacks 03EL on schemes compose to the identity. -/
private theorem representedQuasicoherentSchemeEquivalence_map_pullbackTensorIso_hom_inv
    {R U : BigFppfOver B S hS} (s : R ⟶ U)
    (M N : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory) :
    ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
        (quasicoherentPullbackTensorIso B S hS s M N).hom).hom ≫
      ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
        (quasicoherentPullbackTensorIso B S hS s M N).inv).hom = 𝟙 _ :=
  congrArg (fun x => x.hom)
    ((representedQuasicoherentSchemeEquivalence B S hS R).functor.mapIso
      (quasicoherentPullbackTensorIso B S hS s M N)).hom_inv_id

section Concrete

variable {R U : BigFppfOver B S hS} (t s : R ⟶ U)
  {M N K : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
  (τ : quasicoherentPullbackObj B S hS t M ⟶ quasicoherentPullbackObj B S hS s M)
  (σ : quasicoherentPullbackObj B S hS t N ⟶ quasicoherentPullbackObj B S hS s N)
  (κ : quasicoherentPullbackObj B S hS t K ⟶ quasicoherentPullbackObj B S hS s K)
  (m : quasicoherentTensorObj B S hS U M N ⟶ K)

/-- The instance of `AlgebraicGeometry.Space.tensorReading_source_inv` used in
`AlgebraicGeometry.Space.transitionCommutes_representedTensorChartMul`. -/
private theorem representedTensorReading_source_inv (hbs : RepresentedC3TensorCompat B S hS s M N) :
    type_of% (
      tensorReading_source_inv
        (CU := Modules.{u, u} B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        (CV := Modules.{u, u} B S hS (yoneda.obj R)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS R))
      (Ps := (modulePullback B S hS (representedSpaceMap B S hS s)))
      (TU := (representedQuasicoherentSchemeTensorIso B S hS U M N))
      (sA :=
          (modulePullbackTensorIso B S hS (representedSpaceMap B S hS s)
              ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
              ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj))
      (cMs := (modulePullbackRepresentedQuasicoherentIso B S hS s M))
      (cNs := (modulePullbackRepresentedQuasicoherentIso B S hS s N))
      (cMNs :=
          (modulePullbackRepresentedQuasicoherentIso B S hS s
              (quasicoherentTensorObj B S hS U M N)))
      (es :=
          ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
              (quasicoherentPullbackTensorIso B S hS s M N).hom).hom)
      (es' :=
          ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
              (quasicoherentPullbackTensorIso B S hS s M N).inv).hom)
      (TRs :=
          (representedQuasicoherentSchemeTensorIso B S hS R (quasicoherentPullbackObj B S hS s M)
              (quasicoherentPullbackObj B S hS s N)))
      (representedQuasicoherentSchemeEquivalence_map_pullbackTensorIso_hom_inv B S hS s M N) hbs) :=
  tensorReading_source_inv
    (CU := Modules.{u, u} B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (CV := Modules.{u, u} B S hS (yoneda.obj R)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS R))
    (Ps := (modulePullback B S hS (representedSpaceMap B S hS s)))
    (TU := (representedQuasicoherentSchemeTensorIso B S hS U M N))
    (sA :=
        (modulePullbackTensorIso B S hS (representedSpaceMap B S hS s)
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj))
    (cMs := (modulePullbackRepresentedQuasicoherentIso B S hS s M))
    (cNs := (modulePullbackRepresentedQuasicoherentIso B S hS s N))
    (cMNs :=
        (modulePullbackRepresentedQuasicoherentIso B S hS s (quasicoherentTensorObj B S hS U M N)))
    (es :=
        ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
            (quasicoherentPullbackTensorIso B S hS s M N).hom).hom)
    (es' :=
        ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
            (quasicoherentPullbackTensorIso B S hS s M N).inv).hom)
    (TRs :=
        (representedQuasicoherentSchemeTensorIso B S hS R (quasicoherentPullbackObj B S hS s M)
            (quasicoherentPullbackObj B S hS s N)))
    (representedQuasicoherentSchemeEquivalence_map_pullbackTensorIso_hom_inv B S hS s M N) hbs

/-- The instance of `AlgebraicGeometry.Space.tensorReading_target` used in
`AlgebraicGeometry.Space.transitionCommutes_representedTensorChartMul`. -/
private theorem representedTensorReading_target (hbt : RepresentedC3TensorCompat B S hS t M N) :
    type_of% (
      tensorReading_target
        (CU := Modules.{u, u} B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        (CV := Modules.{u, u} B S hS (yoneda.obj R)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS R))
      (Pt := (modulePullback B S hS (representedSpaceMap B S hS t)))
      (TU := (representedQuasicoherentSchemeTensorIso B S hS U M N))
      (tA :=
          (modulePullbackTensorIso B S hS (representedSpaceMap B S hS t)
              ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
              ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj))
      (cMt := (modulePullbackRepresentedQuasicoherentIso B S hS t M))
      (cNt := (modulePullbackRepresentedQuasicoherentIso B S hS t N))
      (cMNt :=
          (modulePullbackRepresentedQuasicoherentIso B S hS t
              (quasicoherentTensorObj B S hS U M N)))
      (et :=
          ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
              (quasicoherentPullbackTensorIso B S hS t M N).hom).hom)
      (TRt :=
          (representedQuasicoherentSchemeTensorIso B S hS R (quasicoherentPullbackObj B S hS t M)
              (quasicoherentPullbackObj B S hS t N)))
      hbt) :=
  tensorReading_target
    (CU := Modules.{u, u} B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (CV := Modules.{u, u} B S hS (yoneda.obj R)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS R))
    (Pt := (modulePullback B S hS (representedSpaceMap B S hS t)))
    (TU := (representedQuasicoherentSchemeTensorIso B S hS U M N))
    (tA :=
        (modulePullbackTensorIso B S hS (representedSpaceMap B S hS t)
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj))
    (cMt := (modulePullbackRepresentedQuasicoherentIso B S hS t M))
    (cNt := (modulePullbackRepresentedQuasicoherentIso B S hS t N))
    (cMNt :=
        (modulePullbackRepresentedQuasicoherentIso B S hS t (quasicoherentTensorObj B S hS U M N)))
    (et :=
        ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
            (quasicoherentPullbackTensorIso B S hS t M N).hom).hom)
    (TRt :=
        (representedQuasicoherentSchemeTensorIso B S hS R (quasicoherentPullbackObj B S hS t M)
            (quasicoherentPullbackObj B S hS t N)))
    hbt

/-- The instance of `AlgebraicGeometry.Space.tensorReading_source_naturality` used in
`AlgebraicGeometry.Space.transitionCommutes_representedTensorChartMul`. -/
private theorem representedTensorReading_source_naturality :
    type_of% (
      tensorReading_source_naturality
        (CU := Modules.{u, u} B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        (CV := Modules.{u, u} B S hS (yoneda.obj R)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS R))
      (Ps := (modulePullback B S hS (representedSpaceMap B S hS s)))
      (Am := ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map m).hom)
      (cKs := (modulePullbackRepresentedQuasicoherentIso B S hS s K))
      (cMNs :=
          (modulePullbackRepresentedQuasicoherentIso B S hS s
              (quasicoherentTensorObj B S hS U M N)))
      (ms :=
          ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
              (quasicoherentPullbackMap B S hS s m)).hom)
      (modulePullbackRepresentedQuasicoherentIso_naturality B S hS s m)) :=
  tensorReading_source_naturality
    (ns := modulePullbackRepresentedQuasicoherentIso_naturality B S hS s m) ..

/-- The instance of `AlgebraicGeometry.Space.tensorReading_tensor` used in
`AlgebraicGeometry.Space.transitionCommutes_representedTensorChartMul`. -/
private theorem representedTensorReading_tensor :
    type_of% (
      tensorReading_tensor
        (CV := Modules.{u, u} B S hS (yoneda.obj R)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS R))
        (iCV := (inferInstance : Category (Modules.{u, u} B S hS (yoneda.obj R)
          (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS R))))
      (TRt :=
          (representedQuasicoherentSchemeTensorIso B S hS R (quasicoherentPullbackObj B S hS t M)
              (quasicoherentPullbackObj B S hS t N)))
      (TRs :=
          (representedQuasicoherentSchemeTensorIso B S hS R (quasicoherentPullbackObj B S hS s M)
              (quasicoherentPullbackObj B S hS s N)))
      (τ := ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map τ).hom)
      (σ := ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map σ).hom)
      (q :=
          ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
              (quasicoherentTensorHom B S hS R τ σ)).hom)
      (representedQuasicoherentSchemeTensorIso_hom_naturality B S hS R τ σ)) :=
  tensorReading_tensor
    (hT := representedQuasicoherentSchemeTensorIso_hom_naturality B S hS R τ σ) ..

/-- The instance of `AlgebraicGeometry.Space.tensorReading_target_naturality` used in
`AlgebraicGeometry.Space.transitionCommutes_representedTensorChartMul`. -/
private theorem representedTensorReading_target_naturality :
    type_of% (
      tensorReading_target_naturality
        (CU := Modules.{u, u} B S hS (yoneda.obj U)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
        (CV := Modules.{u, u} B S hS (yoneda.obj R)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS R))
      (Pt := (modulePullback B S hS (representedSpaceMap B S hS t)))
      (Am := ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map m).hom)
      (cKt := (modulePullbackRepresentedQuasicoherentIso B S hS t K))
      (cMNt :=
          (modulePullbackRepresentedQuasicoherentIso B S hS t
              (quasicoherentTensorObj B S hS U M N)))
      (mt :=
          ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
              (quasicoherentPullbackMap B S hS t m)).hom)
      (modulePullbackRepresentedQuasicoherentIso_naturality B S hS t m)) :=
  tensorReading_target_naturality
    (nt := modulePullbackRepresentedQuasicoherentIso_naturality B S hS t m) ..

/-- The instance of `AlgebraicGeometry.Space.tensorReading_mul` used in
`AlgebraicGeometry.Space.transitionCommutes_representedTensorChartMul`. -/
private theorem representedTensorReading_mul
    (hm : (quasicoherentPullbackTensorIso B S hS t M N).inv ≫ quasicoherentPullbackMap B S hS t m ≫
        κ =
      quasicoherentTensorHom B S hS R τ σ ≫ (quasicoherentPullbackTensorIso B S hS s M N).inv ≫
        quasicoherentPullbackMap B S hS s m) :
    type_of% (
      tensorReading_mul
        (CV := Modules.{u, u} B S hS (yoneda.obj R)
            (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS R))
      (et :=
          ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
              (quasicoherentPullbackTensorIso B S hS t M N).hom).hom)
      (es' :=
          ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
              (quasicoherentPullbackTensorIso B S hS s M N).inv).hom)
      (κ := ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map κ).hom)
      (q :=
          ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
              (quasicoherentTensorHom B S hS R τ σ)).hom)
      (mt :=
          ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
              (quasicoherentPullbackMap B S hS t m)).hom)
      (ms :=
          ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
              (quasicoherentPullbackMap B S hS s m)).hom)
      (representedQuasicoherentSchemeEquivalence_map_comp_eq B S hS t s τ σ κ m hm)) :=
  tensorReading_mul
    (hm := representedQuasicoherentSchemeEquivalence_map_comp_eq B S hS t s τ σ κ m hm) ..

/-- `AlgebraicGeometry.Space.transitionCommutes_representedTensorChartMul` with the attached
transitions and the attached multiplication written out. -/
private theorem representedTensorChartMul_transition_unfolded
    (hbt : RepresentedC3TensorCompat B S hS t M N) (hbs : RepresentedC3TensorCompat B S hS s M N)
    (hm : (quasicoherentPullbackTensorIso B S hS t M N).inv ≫ quasicoherentPullbackMap B S hS t m ≫
        κ =
      quasicoherentTensorHom B S hS R τ σ ≫ (quasicoherentPullbackTensorIso B S hS s M N).inv ≫
        quasicoherentPullbackMap B S hS s m) :
    ((modulePullbackTensorIso B S hS (representedSpaceMap B S hS t)
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj).hom ≫
        (((modulePullbackRepresentedQuasicoherentIso B S hS t M).hom ≫
            ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map τ).hom ≫
            (modulePullbackRepresentedQuasicoherentIso B S hS s M).inv) ⊗ₘ
          ((modulePullbackRepresentedQuasicoherentIso B S hS t N).hom ≫
            ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map σ).hom ≫
            (modulePullbackRepresentedQuasicoherentIso B S hS s N).inv)) ≫
        (modulePullbackTensorIso B S hS (representedSpaceMap B S hS s)
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj).inv) ≫
      (modulePullback B S hS (representedSpaceMap B S hS s)).map
        ((representedQuasicoherentSchemeTensorIso B S hS U M N).inv ≫
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map m).hom) =
    (modulePullback B S hS (representedSpaceMap B S hS t)).map
        ((representedQuasicoherentSchemeTensorIso B S hS U M N).inv ≫
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map m).hom) ≫
      (modulePullbackRepresentedQuasicoherentIso B S hS t K).hom ≫
        ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map κ).hom ≫
        (modulePullbackRepresentedQuasicoherentIso B S hS s K).inv :=
  transition_tensor_of_readings
    (CU := Modules.{u, u} B S hS (yoneda.obj U)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS U))
    (CV := Modules.{u, u} B S hS (yoneda.obj R)
        (AlgebraicGeometry.isAlgebraicSpace_yoneda B S hS R))
    (Pt := (modulePullback B S hS (representedSpaceMap B S hS t)))
    (Ps := (modulePullback B S hS (representedSpaceMap B S hS s)))
    (TU := (representedQuasicoherentSchemeTensorIso B S hS U M N))
    (Am := ((representedQuasicoherentSchemeEquivalence B S hS U).functor.map m).hom)
    (tA :=
        (modulePullbackTensorIso B S hS (representedSpaceMap B S hS t)
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj))
    (sA :=
        (modulePullbackTensorIso B S hS (representedSpaceMap B S hS s)
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
            ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj))
    (cMt := (modulePullbackRepresentedQuasicoherentIso B S hS t M))
    (cNt := (modulePullbackRepresentedQuasicoherentIso B S hS t N))
    (cKt := (modulePullbackRepresentedQuasicoherentIso B S hS t K))
    (cMNt :=
        (modulePullbackRepresentedQuasicoherentIso B S hS t (quasicoherentTensorObj B S hS U M N)))
    (cMs := (modulePullbackRepresentedQuasicoherentIso B S hS s M))
    (cNs := (modulePullbackRepresentedQuasicoherentIso B S hS s N))
    (cKs := (modulePullbackRepresentedQuasicoherentIso B S hS s K))
    (cMNs :=
        (modulePullbackRepresentedQuasicoherentIso B S hS s (quasicoherentTensorObj B S hS U M N)))
    (et :=
        ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
            (quasicoherentPullbackTensorIso B S hS t M N).hom).hom)
    (es' :=
        ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
            (quasicoherentPullbackTensorIso B S hS s M N).inv).hom)
    (TRt :=
        (representedQuasicoherentSchemeTensorIso B S hS R (quasicoherentPullbackObj B S hS t M)
            (quasicoherentPullbackObj B S hS t N)))
    (TRs :=
        (representedQuasicoherentSchemeTensorIso B S hS R (quasicoherentPullbackObj B S hS s M)
            (quasicoherentPullbackObj B S hS s N)))
    (τ := ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map τ).hom)
    (σ := ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map σ).hom)
    (κ := ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map κ).hom)
    (q :=
        ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
            (quasicoherentTensorHom B S hS R τ σ)).hom)
    (mt :=
        ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
            (quasicoherentPullbackMap B S hS t m)).hom)
    (ms :=
        ((representedQuasicoherentSchemeEquivalence B S hS R).functor.map
            (quasicoherentPullbackMap B S hS s m)).hom)
    (h1 := representedTensorReading_source_inv B S hS s hbs)
    (ht := representedTensorReading_target B S hS t hbt)
    (ns' := representedTensorReading_source_naturality B S hS s m)
    (hT' := representedTensorReading_tensor B S hS t s τ σ)
    (nt := representedTensorReading_target_naturality B S hS t m)
    (hm := representedTensorReading_mul B S hS t s τ σ κ m hm) _ rfl _ rfl _ rfl

end Concrete

/-- **The attached multiplication carries the attached transitions to the attached transition.**
Let `t s : R ⟶ U` be morphisms of the big fppf site, `(M, τ)`, `(N, σ)`, `(K, κ)` quasi-coherent
modules on the scheme of `U` with morphisms `τ : t^*M ⟶ s^*M` (and likewise), and
`m : M ⊗ N ⟶ K` a morphism carrying `τ ⊗ σ` to `κ` through Stacks 03EL along `t` and `s`.  If
the identification of Stacks 03DX (2) of a tensor product is compatible with inverse images along
`t` and `s`, then `(M ⊗ N)^a ≅ M^a ⊗ N^a ⟶ K^a` carries `τ^a ⊗ σ^a` (read through Stacks 03EL for
the represented morphisms) to `κ^a`. -/
theorem transitionCommutes_representedTensorChartMul {R U : BigFppfOver B S hS} (t s : R ⟶ U)
    {M N K : (SheafOfModules.isQuasicoherent
      ((BigFppfOver.toScheme B S hS).obj U).ringCatSheaf).FullSubcategory}
    (τ : quasicoherentPullbackObj B S hS t M ⟶ quasicoherentPullbackObj B S hS s M)
    (σ : quasicoherentPullbackObj B S hS t N ⟶ quasicoherentPullbackObj B S hS s N)
    (κ : quasicoherentPullbackObj B S hS t K ⟶ quasicoherentPullbackObj B S hS s K)
    (m : quasicoherentTensorObj B S hS U M N ⟶ K)
    (hbt : RepresentedC3TensorCompat B S hS t M N) (hbs : RepresentedC3TensorCompat B S hS s M N)
    (hm : (quasicoherentPullbackTensorIso B S hS t M N).inv ≫ quasicoherentPullbackMap B S hS t m ≫
        κ =
      quasicoherentTensorHom B S hS R τ σ ≫ (quasicoherentPullbackTensorIso B S hS s M N).inv ≫
        quasicoherentPullbackMap B S hS s m) :
    TransitionCommutes B S hS
      ((modulePullbackTensorIso B S hS (representedSpaceMap B S hS t)
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj).hom ≫
        (representedSchemeTransition B S hS t s M τ ⊗ₘ representedSchemeTransition B S hS t s N σ) ≫
        (modulePullbackTensorIso B S hS (representedSpaceMap B S hS s)
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj M).obj
          ((representedQuasicoherentSchemeEquivalence B S hS U).functor.obj N).obj).inv)
      (representedSchemeTransition B S hS t s K κ) (representedTensorChartMul B S hS m) := by
  unfold TransitionCommutes
  exact representedTensorChartMul_transition_unfolded B S hS t s τ σ κ m hbt hbs hm

section Descent

attribute [local irreducible] CategoryTheory.yoneda

variable {B S hS} {X : AlgebraicSpaces B S hS}
  (P : Presentation B S hS X.obj X.property)
  {M N K : (SheafOfModules.isQuasicoherent
    ((BigFppfOver.toScheme B S hS).obj P.U).ringCatSheaf).FullSubcategory}
  (τ : quasicoherentPullbackObj B S hS P.target M ⟶ quasicoherentPullbackObj B S hS P.source M)
  (hc : PresentationSchemeCocycle P M τ) (hu : PresentationSchemeUnit P M τ)
  (σ : quasicoherentPullbackObj B S hS P.target N ⟶ quasicoherentPullbackObj B S hS P.source N)
  (hc' : PresentationSchemeCocycle P N σ) (hu' : PresentationSchemeUnit P N σ)
  (κ : quasicoherentPullbackObj B S hS P.target K ⟶ quasicoherentPullbackObj B S hS P.source K)
  (hc'' : PresentationSchemeCocycle P K κ) (hu'' : PresentationSchemeUnit P K κ)
  (m : quasicoherentTensorObj B S hS P.U M N ⟶ K)
  (hbt : RepresentedC3TensorCompat B S hS P.target M N)
  (hbs : RepresentedC3TensorCompat B S hS P.source M N)
  (hm : (quasicoherentPullbackTensorIso B S hS P.target M N).inv ≫
      quasicoherentPullbackMap B S hS P.target m ≫ κ =
    quasicoherentTensorHom B S hS P.R τ σ ≫
        (quasicoherentPullbackTensorIso B S hS P.source M N).inv ≫
      quasicoherentPullbackMap B S hS P.source m)

include hbt hbs hm in
/-- The attached multiplication at a presentation satisfies the hypothesis of
`AlgebraicGeometry.Space.existsUnique_presentationDescendedTensorHom`. -/
theorem transitionCommutes_presentationTensorChartMul :
    TransitionCommutes B S hS (U := (presentationGroupoid P).objects)
      (V := (presentationGroupoid P).arrows) (a := (presentationGroupoid P).target)
      (b := (presentationGroupoid P).source)
      ((modulePullbackTensorIso B S hS (presentationGroupoid P).target
          ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj
          ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj N).obj).hom ≫
        (presentationSchemeTransition P M τ ⊗ₘ presentationSchemeTransition P N σ) ≫
        (modulePullbackTensorIso B S hS (presentationGroupoid P).source
          ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj M).obj
          ((representedQuasicoherentSchemeEquivalence B S hS P.U).functor.obj N).obj).inv)
      (presentationSchemeTransition P K κ) (representedTensorChartMul B S hS m) := by
  have key := transitionCommutes_representedTensorChartMul B S hS P.target P.source τ σ κ m
    hbt hbs hm
  exact key

/-- **The descended multiplication**: the morphism `D(M) ⊗ D(N) ⟶ D(K)` of descended
`𝒪_X`-modules whose inverse image along the atlas is `(M ⊗ N)^a ≅ M^a ⊗ N^a ⟶ K^a`, through
Stacks 03EL and the chart identifications. -/
def presentationDescendedMul :
    (presentationDescendedModule P M τ hc hu).obj ⊗
        (presentationDescendedModule P N σ hc' hu').obj ⟶
      (presentationDescendedModule P K κ hc'' hu'').obj :=
  presentationDescendedTensorHom P τ hc hu σ hc' hu' κ hc'' hu''
    (representedTensorChartMul B S hS m)
    (transitionCommutes_presentationTensorChartMul P τ σ κ m hbt hbs hm)

/-- **The inverse image along the atlas of the descended multiplication is the attached
multiplication**, through Stacks 03EL and the chart identifications. -/
theorem presentationDescendedMul_spec :
    (modulePullback B S hS (presentationAtlas P)).map
        (presentationDescendedMul P τ hc hu σ hc' hu' κ hc'' hu'' m hbt hbs hm) ≫
        (presentationDescendedModuleChartIso P K κ hc'' hu'').hom =
      (modulePullbackTensorIso B S hS (presentationAtlas P)
          (presentationDescendedModule P M τ hc hu).obj
          (presentationDescendedModule P N σ hc' hu').obj).hom ≫
        ((presentationDescendedModuleChartIso P M τ hc hu).hom ⊗ₘ
          (presentationDescendedModuleChartIso P N σ hc' hu').hom) ≫
        representedTensorChartMul B S hS m :=
  presentationDescendedTensorHom_spec P τ hc hu σ hc' hu' κ hc'' hu''
    (representedTensorChartMul B S hS m)
    (transitionCommutes_presentationTensorChartMul P τ σ κ m hbt hbs hm)

/-- **The descended multiplication is unique**: a morphism `D(M) ⊗ D(N) ⟶ D(K)` whose inverse
image along the atlas is the attached multiplication is the descended multiplication. -/
theorem presentationDescendedMul_unique
    (ψ : (presentationDescendedModule P M τ hc hu).obj ⊗
        (presentationDescendedModule P N σ hc' hu').obj ⟶
      (presentationDescendedModule P K κ hc'' hu'').obj)
    (hψ : (modulePullback B S hS (presentationAtlas P)).map ψ ≫
        (presentationDescendedModuleChartIso P K κ hc'' hu'').hom =
      (modulePullbackTensorIso B S hS (presentationAtlas P)
          (presentationDescendedModule P M τ hc hu).obj
          (presentationDescendedModule P N σ hc' hu').obj).hom ≫
        ((presentationDescendedModuleChartIso P M τ hc hu).hom ⊗ₘ
          (presentationDescendedModuleChartIso P N σ hc' hu').hom) ≫
        representedTensorChartMul B S hS m) :
    ψ = presentationDescendedMul P τ hc hu σ hc' hu' κ hc'' hu'' m hbt hbs hm :=
  presentationDescendedTensorHom_unique P τ hc hu σ hc' hu' κ hc'' hu''
    (representedTensorChartMul B S hS m)
    (transitionCommutes_presentationTensorChartMul P τ σ κ m hbt hbs hm) ψ hψ

end Descent

end AlgebraicGeometry.Space

end
