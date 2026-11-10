module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsBaseChangeTensor
public import StacksFrontier.Deformation.Artin.Obstruction.SectionsReductionIdentity

/-!
# The short exact sequence of a deformation situation, and the boundary of a section

Let `S` be a scheme, `q : W → S` a morphism of schemes and `𝓕` an `𝒪_W`-module, and let
`A' → A` be a deformation situation over `S`: a surjection of `S`-algebras in the big fppf site
whose kernel `I` has square zero. Clause (2) of Stacks 07YH considers the short exact sequence
```
0 → 𝓕_A ⊗_A I → 𝓕_{A'} → 𝓕_A → 0
```
and the image of a section `x ∈ H⁰(W_A, 𝓕_A)` under its boundary map. This file gives the sequence
in the spelling the fields of a deformation situation use — the base `Spec A ⟶ S` of the object,
the top `Spec A' ⟶ S` of the situation, and the morphism `Spec A ⟶ Spec A'` over `S` between them,
with no transport between `W_A` and the fibre product over `Spec φ ≫ (Spec A' ⟶ S)` — and
proves condition (iii) of Stacks 07YG for it: the boundary of `x` vanishes exactly when `x` is the
restriction of a section of `𝓕_{A'}`.

The sequence lives on `W_{A'}`: it is `M ↦ 𝓕_{A'} ⊗_{A'} M` applied to `0 → I → A' → A → 0`, which
is exact by flatness (`tensorSheafFunctor_shortExact`). Its outer terms are read as direct images
from `W_A` along the base-change immersion `i : W_A → W_{A'}`, through
`𝓕_{A'} ⊗_{A'} M ≅ i_*(𝓕_A ⊗_A M)`, which is affine base change ([Stacks, Tag 02KG]) followed by
the projection formula of a closed immersion ([Stacks, Tag 0FZE]). The section `x` is read on
`W_{A'}` through `Γ(W_{A'}, i_* G) = Γ(W_A, G)`.

The lifting criterion then rests on one identification of morphisms of sheaves: the third map
of the sequence,
```
𝓕_{A'} ≅ 𝓕_{A'} ⊗_{A'} A' ⟶ 𝓕_{A'} ⊗_{A'} A ≅ i_*(𝓕_A ⊗_A A) ≅ i_* 𝓕_A,
```
is the canonical reduction — the unit of `i^* ⊣ i_*` followed by `i_*` of `i^* 𝓕_{A'} ≅ 𝓕_A` —
whose global-sections component is the restriction map of the functor of sections
(`sectionsPresheafOver_map_eq_reductionMapGen`).

## Main definitions

* `Deformation.Artin.SectionsSheaf.thickeningOver` — the morphism `Spec A → Spec A'` over `S`.
* `Deformation.Artin.SectionsSheaf.kernelShortComplex` — `0 → I → A' → A → 0` as `A'`-modules.
* `Deformation.Artin.SectionsSheaf.pushforwardTensorSheafIsoGen` — `𝓕' ⊗_{A'} M ≅ i_*(𝓕 ⊗_A M)`
  at an arbitrary cartesian square over `Spec A → Spec A'` with `i` a closed immersion, and
  `Deformation.Artin.SectionsSheaf.pushforwardTensorSheafIsoOver` its instance at the base-change
  square of a morphism of schemes over `S`.
* `Deformation.Artin.SectionsSheaf.sectionTransportOver` and
  `Deformation.Artin.SectionsSheaf.thickeningSection` — a section of `𝓕_A` read on `W_{A'}`.
* `Deformation.Artin.SectionsSheaf.thickeningClass` — **the boundary of a section**, computed on
  `W_{A'}`, its first term read as the direct image of `𝓕_A ⊗_A I`.

## Main results

* `Deformation.Artin.SectionsSheaf.isThickening_thickeningOver` and
  `isClosedImmersion_thickening` — `Spec A → Spec A'` is a thickening, so its base change
  `W_A → W_{A'}` is a closed immersion.
* `Deformation.Artin.SectionsSheaf.kernelShortComplex_shortExact`.
* `Deformation.Artin.SectionsSheaf.pushforwardTensorSheafIsoOver_hom_naturality` — the
  identification is natural in the module.
* `Deformation.Artin.SectionsSheaf.thirdMap_eq` — **the third map of the sequence is the
  canonical reduction**, at an arbitrary cartesian square.
* `Deformation.Artin.SectionsSheaf.thickeningClass_eq_zero_iff` — **condition (iii)**: the
  boundary of `x` vanishes iff `x` is the restriction of a section over `A'`.

## Implementation notes

The identification `𝓕' ⊗_{A'} M ≅ i_*(𝓕 ⊗_A M)` and the third-map equation are proved at an
arbitrary cartesian square of schemes, with every scheme and morphism a variable, and only then
instantiated; `pushforwardTensorSheafIsoOver` instantiates the general isomorphism at the raw fibre
products `pullback (Over.mk t).hom q`, while its statement is in the spelling `topProj`/`topSheaf`.

Two costs of the kernel govern the layout.

* `tensorSheafFunctor π 𝓕` is built from the tensor functor
  `Stacks.SheafOfModules.Tensor.sheafTensor` flipped at `𝓕`, the projection formula and the
  unitors from its uncurried bifunctor
  `Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨_, _⟩)`. The two are
  definitionally equal,
  but the kernel needs about 30 s (on objects about 8 s) to see it. The comparison is therefore
  made once, in `tensorSheafFunctor_eq_comp`, and once for the unitor, in
  `eqToHom_comp_tensorSheafFunctorObjSelf_hom`; every later use goes through these with explicit
  `eqToHom` transports and abstract assembly lemmas (`tensorChain_naturality`,
  `comp_eq_of_thirdMap_factors`), so that all later checks are syntactic.
* `topProj t q`, `topSheaf t q 𝓕` and `topScheme t q` unfold to the raw fibre-product spelling,
  and comparing two single terms that differ only in that spelling is cheap. Inside a composite of
  morphisms it is not: when the two sides contain isomorphisms (or adjunctions) that are not
  syntactically identical, the kernel reduces the projections `Iso.hom`, `Iso.inv`,
  `Adjunction.unit` of both by full weak-head normalisation and compares what comes out, and on a
  composite through `pushforwardTensorSheafIsoGen` or the unit of `i^* ⊣ i_*` this exhausts the
  heartbeat budget. Instances: an `Iso.hom` of `pushforwardTensorSheafIsoOver` against the
  `pushforwardTensorSheafIsoGen` it unfolds to, inside a composite, times out, and the same
  comparison after `rw [pushforwardTensorSheafIsoOver_eq]` takes 0.2 s; two copies of
  `pushforwardTensorSheafIsoGen` differing only in the spelling of `ModuleCat.of A A` inside a
  composite time out; the unit of `i^* ⊣ i_*` with `topScheme` against `pullback` implicit
  arguments times out. The cure used throughout is to make the isomorphisms on the two sides
  syntactically identical before the kernel compares them — by rewriting with `rfl` lemmas
  (`pushforwardTensorSheafIsoOver_eq`, `reductionMapGen_eq_unit_comp`), and by naming the transport
  of a section once, at variable data, in `sectionTransportOver`, so that the module
  `ModuleCat.of A A` occurs in the same spelling in the definition of `thickeningSection` and in
  the lifting criterion `exists_preimage_iff_exists_restriction_top`. The remaining change of
  spelling, between `topProj`/`topSheaf` and the raw fibre products, is made in
  `exists_preimage_iff_exists_restriction_top`, on statements about sections in which the
  isomorphisms already agree.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
* [Stacks Project, Tag 02KG](https://stacks.math.columbia.edu/tag/02KG)
* [Stacks Project, Tag 0FZE](https://stacks.math.columbia.edu/tag/0FZE)
* [Stacks Project, Tag 01I9](https://stacks.math.columbia.edu/tag/01I9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry
open scoped CategoryTheory.Prod

universe u

namespace Deformation.Artin.SectionsSheaf

/-! ### The thickening of a deformation situation -/

/-- The spectrum of a surjection of commutative rings whose kernel consists of nilpotent elements
is a thickening. -/
theorem isThickening_specMap_of_surjective {R T : Type u} [CommRing R] [CommRing T]
    (f : R →+* T) (hf : Function.Surjective f)
    (hker : ∀ x ∈ RingHom.ker f, IsNilpotent x) :
    Stacks.Thickenings.IsThickening (Spec.map (CommRingCat.ofHom f)) := by
  refine ⟨IsClosedImmersion.spec_of_surjective _ hf, ?_⟩
  change Function.Surjective (PrimeSpectrum.comap f)
  have h₁ := PrimeSpectrum.isClosedEmbedding_comap_of_surjective _ _ hf
  have h₂ : DenseRange (PrimeSpectrum.comap f) :=
    (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical f).mpr
      fun x hx => mem_nilradical.mpr (hker x hx)
  rw [← Set.range_eq_univ, ← h₁.isClosed_range.closure_eq]
  exact h₂.closure_range

section Thickening

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {a : SiteAlgebra B S hS}

/-- The morphism `Spec A → Spec A'` of schemes over `S` of a deformation situation `A' → A`. -/
def thickeningOver (t : DeformationSituation B S hS a) :
    Over.mk a.toScheme ⟶ Over.mk t.top.toScheme :=
  (Over.post B.inclusion).map t.hom.specMap

/-- The morphism `Spec A → Spec A'` of a deformation situation is `Spec` of `A' → A`. -/
theorem thickeningOver_left (t : DeformationSituation B S hS a) :
    (thickeningOver t).left = Spec.map (CommRingCat.ofHom t.hom.ringMap) :=
  t.hom.specMap_spec

/-- The kernel of a deformation situation consists of nilpotent elements. -/
theorem isNilpotent_of_mem_ker (t : DeformationSituation B S hS a) {x : t.top.carrier}
    (hx : x ∈ RingHom.ker t.hom.ringMap) : IsNilpotent x := by
  refine ⟨2, ?_⟩
  have h := Ideal.pow_mem_pow hx 2
  rwa [t.sq_eq_bot, Ideal.mem_bot] at h

/-- **`Spec A → Spec A'` is a thickening**: `A' → A` is surjective with square-zero kernel. -/
theorem isThickening_thickeningOver (t : DeformationSituation B S hS a) :
    Stacks.Thickenings.IsThickening (thickeningOver t).left := by
  rw [thickeningOver_left]
  exact isThickening_specMap_of_surjective _ t.surjective fun _ hx => isNilpotent_of_mem_ker t hx

/-- **The base-change immersion `W_A → W_{A'}` of a deformation situation is a closed
immersion**, as a base change of a thickening. -/
theorem isClosedImmersion_thickening {W : Scheme.{u}} (q : W ⟶ S)
    (t : DeformationSituation B S hS a) :
    IsClosedImmersion (baseChangeMap q (thickeningOver t)) :=
  isClosedImmersion_baseChangeMap q _ (isThickening_thickeningOver t)

/-! ### The sequence `0 → I → A' → A → 0` -/

/-- The inclusion of the kernel `I` of a deformation situation into `A'`, as a map of
`A'`-modules. -/
def kernelInclusion (t : DeformationSituation B S hS a) :
    (ModuleCat.restrictScalars t.hom.ringMap).obj t.kernelObj ⟶
      ModuleCat.of t.top.carrier t.top.carrier :=
  ModuleCat.ofHom (X := (ModuleCat.restrictScalars t.hom.ringMap).obj t.kernelObj)
    (Y := ModuleCat.of t.top.carrier t.top.carrier)
    { toFun := t.kernelVal
      map_add' := fun _ _ => rfl
      map_smul' := fun r z => by
        let := t.kernelModule
        exact congrArg Subtype.val (Stacks.Smooth.kerModule_smul t.surjective t.sq_eq_bot r z) }

/-- **The sequence `0 → I → A' → A → 0` of a deformation situation**, as a short complex of
`A'`-modules. -/
def kernelShortComplex (t : DeformationSituation B S hS a) :
    ShortComplex (ModuleCat.{u} t.top.carrier) :=
  ShortComplex.mk (kernelInclusion t)
    (quotCoeff (CommRingCat.ofHom t.hom.ringMap) :
      ModuleCat.of t.top.carrier t.top.carrier ⟶
        (ModuleCat.restrictScalars t.hom.ringMap).obj (ModuleCat.of a.carrier a.carrier)) <| by
    ext z
    change t.hom.ringMap (t.kernelVal z) = 0
    exact RingHom.mem_ker.mp z.2

/-- The first term of `kernelShortComplex` is the kernel, with scalars restricted along
`A' → A`. -/
theorem kernelShortComplex_X₁ (t : DeformationSituation B S hS a) :
    (kernelShortComplex t).X₁ =
      (ModuleCat.restrictScalars (CommRingCat.ofHom t.hom.ringMap).hom).obj t.kernelObj :=
  rfl

/-- The last term of `kernelShortComplex` is `A`, with scalars restricted along `A' → A`. -/
theorem kernelShortComplex_X₃ (t : DeformationSituation B S hS a) :
    (kernelShortComplex t).X₃ =
      (ModuleCat.restrictScalars (CommRingCat.ofHom t.hom.ringMap).hom).obj
        (ModuleCat.of a.carrier a.carrier) :=
  rfl

/-- The second map of `kernelShortComplex` is `A' → A`. -/
theorem kernelShortComplex_g (t : DeformationSituation B S hS a) :
    (kernelShortComplex t).g = quotCoeff (CommRingCat.ofHom t.hom.ringMap) :=
  rfl

/-- **`0 → I → A' → A → 0` is short exact.** -/
theorem kernelShortComplex_shortExact (t : DeformationSituation B S hS a) :
    (kernelShortComplex t).ShortExact :=
  ModuleCat.shortComplex_shortExact _
    (fun y => by
      change t.hom.ringMap y = 0 ↔ y ∈ Set.range t.kernelVal
      exact ⟨fun hy => ⟨⟨y, RingHom.mem_ker.mpr hy⟩, rfl⟩,
        fun ⟨z, hz⟩ => hz ▸ RingHom.mem_ker.mp z.2⟩)
    (fun _ _ h => Subtype.val_injective h) t.surjective

end Thickening

/-! ### The identification `𝓕' ⊗_{A'} M ≅ i_*(𝓕 ⊗_A M)` at a cartesian square -/

section Gen

variable {A' A : CommRingCat.{u}} (φ : A' ⟶ A) {X' X : Scheme.{u}} (π' : X' ⟶ Spec A')
  (π : X ⟶ Spec A) (i : X ⟶ X') (hsq : IsPullback π i (Spec.map φ) π')
  (F' : X'.Modules) (F : X.Modules) (e : (Scheme.Modules.pullback i).obj F' ≅ F)

/-- Affine base change at a cartesian square over `Spec φ`. -/
def affineBaseChangeIsoGen (N : (Spec A).Modules) [N.IsQuasicoherent] :
    (Scheme.Modules.pullback π').obj ((Scheme.Modules.pushforward (Spec.map φ)).obj N) ≅
      (Scheme.Modules.pushforward i).obj ((Scheme.Modules.pullback π).obj N) :=
  haveI := Stacks.AlgebraicGeometry.AffineBaseChangeIso.isIso_baseChangeNatTrans_of_isAffineHom
    hsq N
  asIso ((Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).app N)

/-- The projection formula at a closed immersion, in the `Scheme.Modules` spelling. -/
def projectionFormulaIsoGen [IsClosedImmersion i] (G : X.Modules) :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X'.toRingedSpace)).presheaf, ((X'.toRingedSpace)).IsSheaf⟩))).obj
        ((Scheme.Modules.pushforward i).obj G, F') ≅
      (Scheme.Modules.pushforward i).obj
        (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).obj
          (G, (Scheme.Modules.pullback i).obj F')) :=
  _root_.Stacks.AffineProjectionFormula.closedImmersionProjectionFormulaIso i G F'

/-- **`𝓕' ⊗_{A'} M ≅ i_*(𝓕 ⊗_A M)`** at a cartesian square
```
X  --i-->  X'
|π         |π'
Spec A --> Spec A'
```
with `i` a closed immersion, for `𝓕` identified with `i^* 𝓕'`. -/
def pushforwardTensorSheafIsoGen [IsClosedImmersion i] (M : ModuleCat.{u} A) :
    (tensorSheafFunctor π' F').obj ((ModuleCat.restrictScalars φ.hom).obj M) ≅
      (Scheme.Modules.pushforward i).obj ((tensorSheafFunctor π F).obj M) :=
  eqToIso (tensorSheafFunctor_obj_eq π' F' _) ≪≫
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X'.toRingedSpace)).presheaf, ((X'.toRingedSpace)).IsSheaf⟩))).mapIso
      (Iso.prod ((Scheme.Modules.pullback π').mapIso (tildePushforwardIso φ M).symm ≪≫
        affineBaseChangeIsoGen φ π' π i hsq ((tilde.functor A).obj M)) (Iso.refl F')) ≪≫
    projectionFormulaIsoGen i F' ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj M)) ≪≫
    (Scheme.Modules.pushforward i).mapIso
      (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).mapIso
        (Iso.prod (Iso.refl _) e)) ≪≫
    (Scheme.Modules.pushforward i).mapIso (eqToIso (tensorSheafFunctor_obj_eq π F M)).symm

/-- `pushforwardTensorSheafIsoGen` on `hom`, as the composite of the five arrows it is built
from. -/
theorem pushforwardTensorSheafIsoGen_hom [IsClosedImmersion i] (M : ModuleCat.{u} A) :
    (pushforwardTensorSheafIsoGen φ π' π i hsq F' F e M).hom =
      eqToHom (tensorSheafFunctor_obj_eq π' F' ((ModuleCat.restrictScalars φ.hom).obj M)) ≫
        ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
              ⟨((X'.toRingedSpace)).presheaf, ((X'.toRingedSpace)).IsSheaf⟩))).map
          (((Scheme.Modules.pullback π').map (tildePushforwardIso φ M).inv ≫
              (affineBaseChangeIsoGen φ π' π i hsq ((tilde.functor A).obj M)).hom) ×ₘ 𝟙 F') ≫
        (projectionFormulaIsoGen i F'
          ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj M))).hom ≫
        (Scheme.Modules.pushforward i).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).map
            (𝟙 ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj M)) ×ₘ e.hom)) ≫
        (Scheme.Modules.pushforward i).map (eqToHom (tensorSheafFunctor_obj_eq π F M).symm) :=
  rfl

end Gen

/-! ### The two spellings of `𝓕 ⊗_R M`

`tensorSheafFunctor π 𝓕` is built from `Stacks.SheafOfModules.Tensor.sheafTensor` flipped at `𝓕`,
while the projection formula and the unitors are stated for its uncurried bifunctor
`Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor ⟨_, _⟩)`. The two are
definitionally equal, but the kernel pays tens of seconds for the comparison, and pays it again
at every place where a term in one spelling is checked against a type in the other. The
comparison is therefore made exactly twice, in `tensorSheafFunctor_eq_comp` and
`eqToHom_comp_tensorSheafFunctorObjSelf_hom`; everything after them is stated with explicit
`eqToHom` transports, so that every later check is syntactic. -/

section Spelling

open RingedSpaceModuleAdjunction Stacks.RingedSpace

variable {R : CommRingCat.{u}} {X : Scheme.{u}} (π : X ⟶ Spec R)
  (F : SheafOfModules.{u} X.ringCatSheaf)

/-- `M ↦ 𝓕 ⊗_R M` is the tensor product by `𝓕` precomposed with `M ↦ π^* M̃`. -/
theorem tensorSheafFunctor_eq_comp :
    tensorSheafFunctor π F =
      tilde.functor R ⋙ Scheme.Modules.pullback π ⋙
        (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩).flip.obj F :=
  rfl

/-- `M ↦ 𝓕 ⊗_R M` on morphisms, in the bifunctor spelling, with the transports explicit.

The functor tensors on the right by `𝓕`, so its value on a morphism is one sheafified
`PresheafOfModules.tensorHom`; the uncurried bifunctor composes two of them, and
`Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map` is the one step that merges the pair.

The two transports are `eqToHom` of an equality whose two sides are definitionally equal, so each
is the identity and the two unitors of the category cancel them; written in term mode, because the
motive `rw` builds for that cancellation crosses between `X.ringCatSheaf` and
`structureRingSheaf X.toRingedSpace` and is refused at the `implicit` transparency level. -/
theorem tensorSheafFunctor_map_eq_eqToHom {M N : ModuleCat.{u} R} (g : M ⟶ N) :
    (tensorSheafFunctor π F).map g =
      eqToHom (tensorSheafFunctor_obj_eq π F M) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩)).map
          ((Scheme.Modules.pullback π).map ((tilde.functor R).map g) ×ₘ 𝟙 F) ≫
        eqToHom (tensorSheafFunctor_obj_eq π F N).symm :=
  ((Category.id_comp _).trans
      ((Category.comp_id _).trans
        (Stacks.SheafOfModules.Tensor.sheafTensor_uncurry_map
          ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩
          ((Scheme.Modules.pullback π).map ((tilde.functor R).map g)) (𝟙 F)))).symm

/-- The unitor `𝓕 ⊗_R R ≅ 𝓕` in the bifunctor spelling, with the transport explicit. -/
theorem eqToHom_comp_tensorSheafFunctorObjSelf_hom :
    eqToHom (tensorSheafFunctor_obj_eq π F (ModuleCat.of R R)).symm ≫
        (tensorSheafFunctorObjSelf π F).hom =
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩)).map
          ((modulePullbackObjUnitIso π.toLRSHom.toShHom).hom ×ₘ 𝟙 F) ≫
        (tensorSheafUnitLeftIso X.toRingedSpace F).hom :=
  rfl

end Spelling

/-- A functor on a product category sends a composite of products of morphisms to the product
of the composites. -/
private theorem map_prodMk_comp {𝒞 𝒟 ℰ : Type*} [Category 𝒞] [Category 𝒟] [Category ℰ]
    (L : 𝒞 × 𝒟 ⥤ ℰ) {P Q R : 𝒞} {S T U : 𝒟} (f : P ⟶ Q) (g : Q ⟶ R) (f' : S ⟶ T) (g' : T ⟶ U) :
    L.map (f ×ₘ f') ≫ L.map (g ×ₘ g') = L.map ((f ≫ g) ×ₘ (f' ≫ g')) :=
  (L.map_comp _ _).symm

/-- **Naturality of a chain of the shape of `pushforwardTensorSheafIsoGen`, in the abstract.**
Every arrow is a variable constrained by an equation, the transports included. -/
theorem tensorChain_naturality {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (L : 𝒞 × 𝒞 ⥤ 𝒞) (L' : 𝒟 × 𝒟 ⥤ 𝒟) (G : 𝒟 ⥤ 𝒞)
    {U U₁ Q Z Z₁ : 𝒞} {V V₁ Q₁ Y T T₁ : 𝒟}
    (a : U ⟶ U₁) (v : V ⟶ V₁) (u : U ⟶ G.obj V) (u₁ : U₁ ⟶ G.obj V₁)
    (P : L.obj (G.obj V, Q) ⟶ G.obj (L'.obj (V, Q₁)))
    (P₁ : L.obj (G.obj V₁, Q) ⟶ G.obj (L'.obj (V₁, Q₁))) (b : Q₁ ⟶ Y) (k : Q₁ ⟶ Q₁)
    (E : Z ⟶ L.obj (U, Q)) (E₁ : Z₁ ⟶ L.obj (U₁, Q)) (E₁' : L.obj (U₁, Q) ⟶ Z₁)
    (D : T ⟶ L'.obj (V, Y)) (D' : L'.obj (V, Y) ⟶ T) (D₁' : L'.obj (V₁, Y) ⟶ T₁)
    (m : Z ⟶ Z₁) (n : T ⟶ T₁) (p : Z ⟶ G.obj T) (p₁ : Z₁ ⟶ G.obj T₁)
    (hE₁ : E₁' ≫ E₁ = 𝟙 _) (hD : D' ≫ D = 𝟙 _)
    (hm : m = E ≫ L.map (a ×ₘ 𝟙 Q) ≫ E₁') (hn : n = D ≫ L'.map (v ×ₘ 𝟙 Y) ≫ D₁')
    (hp : p = E ≫ L.map (u ×ₘ 𝟙 Q) ≫ P ≫ G.map (L'.map (𝟙 V ×ₘ b)) ≫ G.map D')
    (hp₁ : p₁ = E₁ ≫ L.map (u₁ ×ₘ 𝟙 Q) ≫ P₁ ≫ G.map (L'.map (𝟙 V₁ ×ₘ b)) ≫ G.map D₁')
    (hu : a ≫ u₁ = u ≫ G.map v)
    (hk : k = 𝟙 Q₁) (hP : L.map (G.map v ×ₘ 𝟙 Q) ≫ P₁ = P ≫ G.map (L'.map (v ×ₘ k))) :
    m ≫ p₁ = p ≫ G.map n := by
  subst hm hn hp hp₁ hk
  have h₁ : L.map (a ×ₘ 𝟙 Q) ≫ L.map (u₁ ×ₘ 𝟙 Q) =
      L.map (u ×ₘ 𝟙 Q) ≫ L.map (G.map v ×ₘ 𝟙 Q) := by
    simp only [map_prodMk_comp, hu, Category.comp_id]
  have h₂ : L'.map (v ×ₘ 𝟙 Q₁) ≫ L'.map (𝟙 V₁ ×ₘ b) =
      L'.map (𝟙 V ×ₘ b) ≫ L'.map (v ×ₘ 𝟙 Y) := by
    simp only [map_prodMk_comp, Category.id_comp, Category.comp_id]
  simp only [Category.assoc, ← G.map_comp, reassoc_of% hE₁, reassoc_of% hD]
  rw [← Category.assoc (L.map (a ×ₘ 𝟙 Q)), h₁, Category.assoc, ← Category.assoc _ P₁, hP,
    Category.assoc, ← G.map_comp, ← Category.assoc (L'.map (v ×ₘ 𝟙 Q₁)), h₂, Category.assoc]

section Gen

variable {A' A : CommRingCat.{u}} (φ : A' ⟶ A) {X' X : Scheme.{u}} (π' : X' ⟶ Spec A')
  (π : X ⟶ Spec A) (i : X ⟶ X') (hsq : IsPullback π i (Spec.map φ) π')
  (F' : X'.Modules) (F : X.Modules) (e : (Scheme.Modules.pullback i).obj F' ≅ F)

/-- `tildePushforwardIso` is natural in the module. -/
theorem tildePushforwardIso_inv_naturality {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (tilde.functor A').map ((ModuleCat.restrictScalars φ.hom).map f) ≫
        (tildePushforwardIso φ N).inv =
      (tildePushforwardIso φ M).inv ≫
        (Scheme.Modules.pushforward (Spec.map φ)).map ((tilde.functor A).map f) :=
  (pushforwardTildeIso A' A φ).inv.naturality f

/-- `affineBaseChangeIsoGen` is natural in the module. -/
theorem affineBaseChangeIsoGen_hom_naturality {N₁ N₂ : (Spec A).Modules}
    [N₁.IsQuasicoherent] [N₂.IsQuasicoherent] (g : N₁ ⟶ N₂) :
    (Scheme.Modules.pullback π').map ((Scheme.Modules.pushforward (Spec.map φ)).map g) ≫
        (affineBaseChangeIsoGen φ π' π i hsq N₂).hom =
      (affineBaseChangeIsoGen φ π' π i hsq N₁).hom ≫
        (Scheme.Modules.pushforward i).map ((Scheme.Modules.pullback π).map g) :=
  (Stacks.AlgebraicGeometry.AffinePushforward.baseChangeNatTrans hsq.w).naturality g

/-- `projectionFormulaIsoGen` is natural in the first factor. -/
theorem projectionFormulaIsoGen_hom_naturality [IsClosedImmersion i] {G G' : X.Modules}
    (g : G ⟶ G') :
    ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨((X'.toRingedSpace)).presheaf, ((X'.toRingedSpace)).IsSheaf⟩))).map
          ((Scheme.Modules.pushforward i).map g ×ₘ 𝟙 F') ≫
        (projectionFormulaIsoGen i F' G').hom =
      (projectionFormulaIsoGen i F' G).hom ≫
        (Scheme.Modules.pushforward i).map
          (((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                ⟨((X.toRingedSpace)).presheaf, ((X.toRingedSpace)).IsSheaf⟩))).map
            (g ×ₘ (Scheme.Modules.pullback i).map (𝟙 F'))) :=
  Stacks.AffineProjectionFormula.projectionFormulaMap_natural i.toLRSHom.toShHom g (𝟙 F')

/-- The first-factor arrow of `pushforwardTensorSheafIsoGen` is natural in the module. -/
theorem pushforwardTensorSheafIsoGen_firstFactor_naturality {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (Scheme.Modules.pullback π').map
        ((tilde.functor A').map ((ModuleCat.restrictScalars φ.hom).map f)) ≫
        ((Scheme.Modules.pullback π').map (tildePushforwardIso φ N).inv ≫
          (affineBaseChangeIsoGen φ π' π i hsq ((tilde.functor A).obj N)).hom) =
      ((Scheme.Modules.pullback π').map (tildePushforwardIso φ M).inv ≫
          (affineBaseChangeIsoGen φ π' π i hsq ((tilde.functor A).obj M)).hom) ≫
        (Scheme.Modules.pushforward i).map
          ((Scheme.Modules.pullback π).map ((tilde.functor A).map f)) := by
  rw [← Category.assoc, ← Functor.map_comp, tildePushforwardIso_inv_naturality,
    Functor.map_comp, Category.assoc, affineBaseChangeIsoGen_hom_naturality, Category.assoc]

/-- **`pushforwardTensorSheafIsoGen` is natural in the module.** -/
theorem pushforwardTensorSheafIsoGen_hom_naturality [IsClosedImmersion i]
    {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (tensorSheafFunctor π' F').map ((ModuleCat.restrictScalars φ.hom).map f) ≫
        (pushforwardTensorSheafIsoGen φ π' π i hsq F' F e N).hom =
      (pushforwardTensorSheafIsoGen φ π' π i hsq F' F e M).hom ≫
        (Scheme.Modules.pushforward i).map ((tensorSheafFunctor π F).map f) := by
  exact tensorChain_naturality
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X'.toRingedSpace.presheaf, X'.toRingedSpace.IsSheaf⟩))
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨X.toRingedSpace.presheaf, X.toRingedSpace.IsSheaf⟩))
    (Scheme.Modules.pushforward i)
    ((Scheme.Modules.pullback π').map
      ((tilde.functor A').map ((ModuleCat.restrictScalars φ.hom).map f)))
    ((Scheme.Modules.pullback π).map ((tilde.functor A).map f))
    _ _ _ _ e.hom _ _ _ _ _ _ _ _ _ _ _
    ((eqToHom_trans _ _).trans (eqToHom_refl _ _))
    ((eqToHom_trans _ _).trans (eqToHom_refl _ _))
    (tensorSheafFunctor_map_eq_eqToHom π' F' _) (tensorSheafFunctor_map_eq_eqToHom π F f)
    (pushforwardTensorSheafIsoGen_hom φ π' π i hsq F' F e M)
    (pushforwardTensorSheafIsoGen_hom φ π' π i hsq F' F e N)
    (pushforwardTensorSheafIsoGen_firstFactor_naturality φ π' π i hsq f)
    (CategoryTheory.Functor.map_id _ _)
    (projectionFormulaIsoGen_hom_naturality i F' _)

end Gen

/-! ### The identification at the base-change square of a morphism over `S` -/

section Over

variable {S : Scheme.{u}} {A' A : CommRingCat.{u}} (t : Spec A' ⟶ S) (t' : Spec A ⟶ S)
  (α : Over.mk t' ⟶ Over.mk t) (φ : A' ⟶ A)
  {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)

/-- The base-change square of a morphism `α` of schemes over `S` whose underlying morphism is
`Spec φ`, with `Spec φ` in place of `α.left`. -/
theorem isPullback_baseChangeMap_of_eq (hα : α.left = Spec.map φ) :
    IsPullback (pullback.fst (Over.mk t').hom q) (baseChangeMap q α) (Spec.map φ)
      (pullback.fst (Over.mk t).hom q) :=
  hα ▸ (isPullback_baseChangeMap q α).flip

/-- **`𝓕_{T} ⊗_{A'} M ≅ i_*(𝓕_{T'} ⊗_A M)`** for a morphism `α : T' → T` of schemes over `S`
from `T' = Spec A` to `T = Spec A'` whose underlying morphism is `Spec φ`, and an `A`-module
`M`; here `i : W_{T'} → W_T` is the base-change morphism, assumed to be a closed immersion. -/
def pushforwardTensorSheafIsoOver (hα : α.left = Spec.map φ)
    (hi : IsClosedImmersion (baseChangeMap q α)) (M : ModuleCat.{u} A) :
    (tensorSheafFunctor (topProj t q) (topSheaf t q 𝓕)).obj
        ((ModuleCat.restrictScalars φ.hom).obj M) ≅
      (Scheme.Modules.pushforward (baseChangeMap q α)).obj
        ((tensorSheafFunctor (topProj t' q) (topSheaf t' q 𝓕)).obj M) :=
  letI := hi
  pushforwardTensorSheafIsoGen φ (pullback.fst (Over.mk t).hom q)
    (pullback.fst (Over.mk t').hom q) (baseChangeMap q α)
    (isPullback_baseChangeMap_of_eq t t' α φ q hα)
    ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)
    ((Scheme.Modules.pullback (pullback.snd (Over.mk t').hom q)).obj 𝓕)
    (baseChangeSheafIsoGen _ _ 𝓕 (baseChangeMap q α) (baseChangeMap_comp_snd q α)) M

/-- `pushforwardTensorSheafIsoOver` is `pushforwardTensorSheafIsoGen` at the base-change
square. -/
theorem pushforwardTensorSheafIsoOver_eq (hα : α.left = Spec.map φ)
    (hi : IsClosedImmersion (baseChangeMap q α)) (M : ModuleCat.{u} A) :
    pushforwardTensorSheafIsoOver t t' α φ q 𝓕 hα hi M =
      @pushforwardTensorSheafIsoGen _ _ φ _ _ (pullback.fst (Over.mk t).hom q)
        (pullback.fst (Over.mk t').hom q) (baseChangeMap q α)
        (isPullback_baseChangeMap_of_eq t t' α φ q hα)
        ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)
        ((Scheme.Modules.pullback (pullback.snd (Over.mk t').hom q)).obj 𝓕)
        (baseChangeSheafIsoGen _ _ 𝓕 (baseChangeMap q α) (baseChangeMap_comp_snd q α)) hi M :=
  rfl

/-- `pushforwardTensorSheafIsoOver` is natural in the module. -/
theorem pushforwardTensorSheafIsoOver_hom_naturality (hα : α.left = Spec.map φ)
    (hi : IsClosedImmersion (baseChangeMap q α)) {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    (tensorSheafFunctor (topProj t q) (topSheaf t q 𝓕)).map
          ((ModuleCat.restrictScalars φ.hom).map f) ≫
        (pushforwardTensorSheafIsoOver t t' α φ q 𝓕 hα hi N).hom =
      (pushforwardTensorSheafIsoOver t t' α φ q 𝓕 hα hi M).hom ≫
        (Scheme.Modules.pushforward (baseChangeMap q α)).map
          ((tensorSheafFunctor (topProj t' q) (topSheaf t' q 𝓕)).map f) := by
  rw [pushforwardTensorSheafIsoOver_eq, pushforwardTensorSheafIsoOver_eq]
  exact @pushforwardTensorSheafIsoGen_hom_naturality _ _ φ _ _ (pullback.fst (Over.mk t).hom q)
    (pullback.fst (Over.mk t').hom q) (baseChangeMap q α)
    (isPullback_baseChangeMap_of_eq t t' α φ q hα)
    ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)
    ((Scheme.Modules.pullback (pullback.snd (Over.mk t').hom q)).obj 𝓕)
    (baseChangeSheafIsoGen _ _ 𝓕 (baseChangeMap q α) (baseChangeMap_comp_snd q α)) hi _ _ f

end Over

/-! ### Sections of a direct image along a morphism -/

/-- A global section of `G` read as a global section of `i_* G`: the sections of `i_* G` over
`⊤` are the sections of `G` over `i⁻¹ ⊤ = ⊤`. -/
def pushforwardSection {X X' : Scheme.{u}} (i : X ⟶ X') (G : X.Modules) :
    Γ(G, ⊤) ⟶ Γ((Scheme.Modules.pushforward i).obj G, ⊤) :=
  G.presheaf.map (homOfLE le_top : i ⁻¹ᵁ ⊤ ⟶ ⊤).op

/-- **A section of `𝓕_{T'}` read on `W_T`** as a section of `𝓕_T ⊗_{A'} A`, for a morphism
`α : T' → T` of schemes over `S` from `T' = Spec A` to `T = Spec A'` whose underlying morphism is
`Spec φ` and whose base change `i : W_{T'} → W_T` is a closed immersion: the section is read
through `𝓕_{T'} ≅ 𝓕_{T'} ⊗_A A`, then on `W_T` through `Γ(W_T, i_* G) = Γ(W_{T'}, G)`, and then
through the inverse of `pushforwardTensorSheafIsoOver` at `M = A`. -/
def sectionTransportOver {S : Scheme.{u}} {A' A : CommRingCat.{u}} (t : Spec A' ⟶ S)
    (t' : Spec A ⟶ S) (α : Over.mk t' ⟶ Over.mk t) (φ : A' ⟶ A) {W : Scheme.{u}} (q : W ⟶ S)
    (𝓕 : W.Modules) (hα : α.left = Spec.map φ) (hi : IsClosedImmersion (baseChangeMap q α))
    (x : Γ(topSheaf t' q 𝓕, ⊤)) :
    Γ((tensorSheafFunctor (topProj t q) (topSheaf t q 𝓕)).obj
      ((ModuleCat.restrictScalars φ.hom).obj (ModuleCat.of A A)), ⊤) :=
  Scheme.Modules.Hom.app
    (pushforwardTensorSheafIsoOver t t' α φ q 𝓕 hα hi (ModuleCat.of A A)).inv ⊤
    (pushforwardSection (baseChangeMap q α) _
      (Scheme.Modules.Hom.app (tensorSheafFunctorObjSelf (topProj t' q) (topSheaf t' q 𝓕)).inv ⊤
        x))

/-! ### The boundary of a section, computed on `W_{A'}` -/

section Boundary

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S} {a : SiteAlgebra B S hS}

/-- The section `x` of `𝓕_A` on `W_A` read on `W_{A'}` as a section of `𝓕_{A'} ⊗_{A'} A`, as an
element of the degree-zero term of the cohomology of `W_{A'}`: `sectionTransportOver` at the
thickening of the deformation situation. -/
def thickeningSection {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)
    (t : DeformationSituation B S hS a) (x : Γ(topSheaf a.toScheme q 𝓕, ⊤)) :
    (((cohomologyDeltaFunctor (topProj t.top.toScheme q)).functor 0).obj
      ((tensorSheafFunctor (topProj t.top.toScheme q) (topSheaf t.top.toScheme q 𝓕)).obj
        (kernelShortComplex t).X₃) : Type u) :=
  (zeroIsoSections (topProj t.top.toScheme q)).inv.app _
    (sectionTransportOver t.top.toScheme a.toScheme (thickeningOver t)
      (CommRingCat.ofHom t.hom.ringMap) q 𝓕 (thickeningOver_left t)
      (isClosedImmersion_thickening q t) x)

end Boundary

section Flat

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {Λ : Type u} [CommRing Λ] {hS : B.Contains (Spec (.of Λ))}
  {a : SiteAlgebra B (Spec (.of Λ)) hS} {W : Scheme.{u}} (g : W ⟶ Spec (.of Λ)) (F : W.Modules)
  [F.IsQuasicoherent]

/-- Flatness of `𝓕_{A'}` over `A'`, in the spelling of `topProj` and `topSheaf`. -/
theorem isFlatOver_topSheaf (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F)
    {A' : CommRingCat.{u}} (t : Spec A' ⟶ Spec (.of Λ)) :
    AlgebraicGeometry.IsFlatOver (topProj t g).toLRSHom.toShHom (topSheaf t g F) :=
  isFlatOver_baseChange g F hF t

/-- **The boundary of a section, computed on `W_{A'}`.** For a deformation situation `A' → A`
with kernel `I` and a section `x` of `𝓕_A` on `W_A`, the image of `x` under the connecting
morphism `H⁰(W_{A'}, 𝓕_{A'} ⊗_{A'} A) → H¹(W_{A'}, 𝓕_{A'} ⊗_{A'} I)` of the short exact
sequence `0 → 𝓕_{A'} ⊗_{A'} I → 𝓕_{A'} → 𝓕_{A'} ⊗_{A'} A → 0`, with `x` read on `W_{A'}`
through `𝓕_{A'} ⊗_{A'} A ≅ i_*(𝓕_A ⊗_A A) ≅ i_* 𝓕_A` and the target read through
`𝓕_{A'} ⊗_{A'} I ≅ i_*(𝓕_A ⊗_A I)`. -/
def thickeningClass (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F)
    (t : DeformationSituation B (Spec (.of Λ)) hS a) (x : Γ(topSheaf a.toScheme g F, ⊤)) :
    (((cohomologyDeltaFunctor (topProj t.top.toScheme g)).functor 1).obj
      ((Scheme.Modules.pushforward (baseChangeMap g (thickeningOver t))).obj
        ((tensorSheafFunctor (topProj a.toScheme g) (topSheaf a.toScheme g F)).obj
          t.kernelObj)) : Type u) :=
  (((cohomologyDeltaFunctor (topProj t.top.toScheme g)).functor 1).mapIso
      (eqToIso (congrArg (tensorSheafFunctor (topProj t.top.toScheme g)
          (topSheaf t.top.toScheme g F)).obj (kernelShortComplex_X₁ t)) ≪≫
        pushforwardTensorSheafIsoOver t.top.toScheme a.toScheme (thickeningOver t)
          (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
          (isClosedImmersion_thickening g t) t.kernelObj)).hom
    (obstructionClass (topProj t.top.toScheme g) (topSheaf t.top.toScheme g F)
      (isFlatOver_topSheaf g F hF t.top.toScheme) (kernelShortComplex_shortExact t)
      (thickeningSection g F t x))

end Flat

/-! ### The third map of the sequence is the canonical reduction -/

section ThirdMap

open RingedSpaceModuleAdjunction Stacks.RingedSpace

variable {A' A : CommRingCat.{u}} (φ : A' ⟶ A) {X' X : Scheme.{u}} (π' : X' ⟶ Spec A')
  (π : X ⟶ Spec A) (i : X ⟶ X') (hsq : IsPullback π i (Spec.map φ) π')
  (F' : X'.Modules) (F : X.Modules) (e : (Scheme.Modules.pullback i).obj F' ≅ F)

/-- **The structure-sheaf component of the third map** `𝒪_{X'} ⟶ i_*(π^* Ã)`, obtained from
`A' → A`, the comparison of [Stacks, Tag 01I9] and affine base change. -/
def thirdMapUnit :
    SheafOfModules.unit (structureRingSheaf X'.toRingedSpace) ⟶
      (Scheme.Modules.pushforward i).obj
        ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj (ModuleCat.of A A))) :=
  (modulePullbackObjUnitIso π'.toLRSHom.toShHom).inv ≫
    (Scheme.Modules.pullback π').map ((tilde.functor A').map (quotCoeff φ)) ≫
      (Scheme.Modules.pullback π').map (tildePushforwardIso φ (ModuleCat.of A A)).inv ≫
        (affineBaseChangeIsoGen φ π' π i hsq ((tilde.functor A).obj (ModuleCat.of A A))).hom

/-- `thirdMapUnit` with its two affine factors contracted into the structure morphism of
`Spec φ`. -/
theorem thirdMapUnit_eq :
    thirdMapUnit φ π' π i hsq =
      (modulePullbackObjUnitIso π'.toLRSHom.toShHom).inv ≫
        (Scheme.Modules.pullback π').map
            (Stacks.AlgebraicGeometry.AffineBaseChange.structureUnitHom (Spec.map φ)) ≫
          (affineBaseChangeIsoGen φ π' π i hsq ((tilde.functor A).obj (ModuleCat.of A A))).hom :=
  congrArg
    (fun z => (modulePullbackObjUnitIso π'.toLRSHom.toShHom).inv ≫ z)
    ((Category.assoc _ _ _).symm.trans
      (congrArg
        (fun u => u ≫ (affineBaseChangeIsoGen φ π' π i hsq
          ((tilde.functor A).obj (ModuleCat.of A A))).hom)
        ((Functor.map_comp _ _ _).symm.trans
          (congrArg (fun v => (Scheme.Modules.pullback π').map v)
            (Stacks.AlgebraicGeometry.AffineBaseChange.tilde_map_comp_pushforwardTildeIso_inv
              φ (quotCoeff φ) (map_one φ.hom))))))

/-- **The structure-sheaf component of the third map is the canonical `𝒪_{X'} ⟶ i_* 𝒪_X`.** -/
theorem thirdMapUnit_comp_modulePullbackObjUnitIso :
    thirdMapUnit φ π' π i hsq ≫
        (Scheme.Modules.pushforward i).map (modulePullbackObjUnitIso π.toLRSHom.toShHom).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app
          (SheafOfModules.unit (structureRingSheaf X'.toRingedSpace)) ≫
        (Scheme.Modules.pushforward i).map (modulePullbackObjUnitIso i.toLRSHom.toShHom).hom :=
  ((congrArg
        (fun z => z ≫ (Scheme.Modules.pushforward i).map
          (modulePullbackObjUnitIso π.toLRSHom.toShHom).hom)
        (thirdMapUnit_eq φ π' π i hsq)).trans
      ((Category.assoc _ _ _).trans
        ((congrArg
            (fun z => (modulePullbackObjUnitIso π'.toLRSHom.toShHom).inv ≫ z)
            ((Category.assoc _ _ _).trans
              (Stacks.AlgebraicGeometry.AffineBaseChange.baseChangeNatTrans_structureUnitHom
                hsq.w))).trans
          (Iso.inv_hom_id_assoc _ _)))).trans
    (Stacks.AlgebraicGeometry.AffineBaseChange.unit_comp_map_pullbackUnitIso i).symm

/-- **The unit followed by `i_* e` is the projection-formula composite of the structure-sheaf
component**, in the bifunctor spelling of the tensor product. -/
theorem unit_comp_eq_tensorProjectionFormula [IsClosedImmersion i] :
    (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F' ≫
        (Scheme.Modules.pushforward i).map e.hom =
      (tensorSheafUnitLeftIso X'.toRingedSpace F').inv ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(X'.toRingedSpace).presheaf, (X'.toRingedSpace).IsSheaf⟩)).map
            (thirdMapUnit φ π' π i hsq ×ₘ 𝟙 F') ≫
          (projectionFormulaIsoGen i F'
            ((Scheme.Modules.pullback π).obj ((tilde.functor A).obj (ModuleCat.of A A)))).hom ≫
            (Scheme.Modules.pushforward i).map
              ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
                    ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩)).map
                  ((modulePullbackObjUnitIso π.toLRSHom.toShHom).hom ×ₘ e.hom) ≫
                (tensorSheafUnitLeftIso X.toRingedSpace F).hom) :=
  (Stacks.AlgebraicGeometry.ProjectionFormula.adjunctionTensorMap_leftUnitObj_comp
    (Scheme.Modules.pullbackPushforwardAdjunction i)
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(X'.toRingedSpace).presheaf, (X'.toRingedSpace).IsSheaf⟩))
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩))
    (comparisonNatTrans i.toLRSHom.toShHom)
    (fun Z => tensorSheafUnitLeftIso X'.toRingedSpace Z)
    (fun Z => tensorSheafUnitLeftIso X.toRingedSpace Z)
    (modulePullbackObjUnitIso i.toLRSHom.toShHom)
    (fun u => tensorSheafUnitLeftIso_naturality _ u)
    (fun Z => comparison_leftUnitor i.toLRSHom.toShHom Z)
    (thirdMapUnit φ π' π i hsq)
    (modulePullbackObjUnitIso π.toLRSHom.toShHom).hom
    (thirdMapUnit_comp_modulePullbackObjUnitIso φ π' π i hsq) F' e.hom).symm

end ThirdMap

/-- **The inverse of a unitor read through a transport, in the abstract.** If `E ≫ σ` is the
bifunctor-spelled unitor `L(μ, 1) ≫ λ`, then `σ⁻¹` is `λ⁻¹ ≫ L(μ⁻¹, 1) ≫ E`. -/
theorem iso_inv_eq_of_eqToHom_comp {𝒞 : Type*} [Category 𝒞] (L : 𝒞 × 𝒞 ⥤ 𝒞)
    {Z Y O U : 𝒞} (σ : Z ≅ Y) (μ : U ≅ O) (lam : L.obj (O, Y) ≅ Y)
    (E : L.obj (U, Y) ⟶ Z) (E' : Z ⟶ L.obj (U, Y)) (hE : E' ≫ E = 𝟙 Z)
    (h : E ≫ σ.hom = L.map (μ.hom ×ₘ 𝟙 Y) ≫ lam.hom) :
    σ.inv = lam.inv ≫ L.map (μ.inv ×ₘ 𝟙 Y) ≫ E := by
  have hσ : σ.hom = E' ≫ L.map (μ.hom ×ₘ 𝟙 Y) ≫ lam.hom := by
    rw [← h, reassoc_of% hE]
  refine Iso.inv_ext ?_
  have hμ : L.map (μ.hom ×ₘ 𝟙 Y) ≫ L.map (μ.inv ×ₘ 𝟙 Y) = 𝟙 _ := by
    rw [map_prodMk_comp, Iso.hom_inv_id, Category.comp_id, ← L.map_id]
    rfl
  rw [hσ, Category.assoc, Category.assoc, Iso.hom_inv_id_assoc, reassoc_of% hμ, hE]

/-- **The assembly of the third map, in the abstract.** Four arrows constrained to be the four
factors of the third map of the sheaf-level sequence — the inverse unitor, the map induced by
`A' → A`, the comparison with the direct image and the unitor on `X` — compose to the
projection-formula composite of the single first-factor arrow `r` they amount to. -/
theorem comp_eq_of_thirdMap_factors {𝒞 𝒟 : Type*} [Category 𝒞] [Category 𝒟]
    (L : 𝒞 × 𝒞 ⥤ 𝒞) (L' : 𝒟 × 𝒟 ⥤ 𝒟) (G : 𝒟 ⥤ 𝒞)
    {Q O U₀ U₁ Z₀ Z₁ : 𝒞} {V O₁ Q₁ Y T₀ : 𝒟}
    (ι : Q ⟶ Z₀) (m : Z₀ ⟶ Z₁) (p : Z₁ ⟶ G.obj T₀) (σ : T₀ ⟶ Y)
    (lamInv : Q ⟶ L.obj (O, Q)) (μInv : O ⟶ U₀) (a : U₀ ⟶ U₁) (u : U₁ ⟶ G.obj V)
    (P : L.obj (G.obj V, Q) ⟶ G.obj (L'.obj (V, Q₁))) (b : Q₁ ⟶ Y) (μ : V ⟶ O₁)
    (lam : L'.obj (O₁, Y) ⟶ Y)
    (E₀ : L.obj (U₀, Q) ⟶ Z₀) (E₀' : Z₀ ⟶ L.obj (U₀, Q)) (E₁ : Z₁ ⟶ L.obj (U₁, Q))
    (E₁' : L.obj (U₁, Q) ⟶ Z₁) (D : L'.obj (V, Y) ⟶ T₀)
    (hE₀ : E₀ ≫ E₀' = 𝟙 _) (hE₁ : E₁' ≫ E₁ = 𝟙 _)
    (hι : ι = lamInv ≫ L.map (μInv ×ₘ 𝟙 Q) ≫ E₀)
    (hm : m = E₀' ≫ L.map (a ×ₘ 𝟙 Q) ≫ E₁')
    (hp : p = E₁ ≫ L.map (u ×ₘ 𝟙 Q) ≫ P ≫ G.map (L'.map (𝟙 V ×ₘ b)) ≫ G.map D)
    (hσ : D ≫ σ = L'.map (μ ×ₘ 𝟙 Y) ≫ lam)
    (r : O ⟶ G.obj V) (hr : μInv ≫ a ≫ u = r) :
    ι ≫ m ≫ p ≫ G.map σ =
      lamInv ≫ L.map (r ×ₘ 𝟙 Q) ≫ P ≫ G.map (L'.map (μ ×ₘ b) ≫ lam) := by
  subst hι hm hp hr
  have h₁ : L.map (μInv ×ₘ 𝟙 Q) ≫ L.map (a ×ₘ 𝟙 Q) ≫ L.map (u ×ₘ 𝟙 Q) =
      L.map ((μInv ≫ a ≫ u) ×ₘ 𝟙 Q) := by
    simp only [map_prodMk_comp, Category.comp_id]
  have h₂ : L'.map (𝟙 V ×ₘ b) ≫ L'.map (μ ×ₘ 𝟙 Y) = L'.map (μ ×ₘ b) := by
    simp only [map_prodMk_comp, Category.id_comp, Category.comp_id]
  simp only [Category.assoc, ← G.map_comp, hσ, reassoc_of% hE₀, reassoc_of% hE₁]
  rw [reassoc_of% h₁, reassoc_of% h₂]

section ThirdMapGen

open RingedSpaceModuleAdjunction Stacks.RingedSpace

variable {A' A : CommRingCat.{u}} (φ : A' ⟶ A) {X' X : Scheme.{u}} (π' : X' ⟶ Spec A')
  (π : X ⟶ Spec A) (i : X ⟶ X') (hsq : IsPullback π i (Spec.map φ) π')
  (F' : X'.Modules) (F : X.Modules) (e : (Scheme.Modules.pullback i).obj F' ≅ F)

/-- The inverse unitor `𝓕 ≅ 𝓕 ⊗_R R`, in the bifunctor spelling with the transport explicit. -/
theorem tensorSheafFunctorObjSelf_inv_eq {R : CommRingCat.{u}} {Y : Scheme.{u}}
    (ρ : Y ⟶ Spec R) (G : SheafOfModules.{u} Y.ringCatSheaf) :
    (tensorSheafFunctorObjSelf ρ G).inv =
      (tensorSheafUnitLeftIso Y.toRingedSpace G).inv ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
            ⟨(Y.toRingedSpace).presheaf, (Y.toRingedSpace).IsSheaf⟩)).map
          ((modulePullbackObjUnitIso ρ.toLRSHom.toShHom).inv ×ₘ 𝟙 G) ≫
        eqToHom (tensorSheafFunctor_obj_eq ρ G (ModuleCat.of R R)).symm :=
  iso_inv_eq_of_eqToHom_comp
    (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
      ⟨(Y.toRingedSpace).presheaf, (Y.toRingedSpace).IsSheaf⟩))
    (tensorSheafFunctorObjSelf ρ G)
    (modulePullbackObjUnitIso ρ.toLRSHom.toShHom) (tensorSheafUnitLeftIso Y.toRingedSpace G)
    _ (eqToHom (tensorSheafFunctor_obj_eq ρ G (ModuleCat.of R R)))
    ((eqToHom_trans _ _).trans (eqToHom_refl _ _))
    (eqToHom_comp_tensorSheafFunctorObjSelf_hom ρ G)

/-- **The third map of the sequence is the canonical reduction**, at a cartesian square: the
composite
```
𝓕' ≅ 𝓕' ⊗_{A'} A' ⟶ 𝓕' ⊗_{A'} A ≅ i_*(𝓕 ⊗_A A) ≅ i_* 𝓕
```
is the unit of `i^* ⊣ i_*` followed by the direct image of `e : i^* 𝓕' ≅ 𝓕`. -/
theorem thirdMap_eq [IsClosedImmersion i] :
    (tensorSheafFunctorObjSelf π' F').inv ≫ (tensorSheafFunctor π' F').map (quotCoeff φ) ≫
        (pushforwardTensorSheafIsoGen φ π' π i hsq F' F e (ModuleCat.of A A)).hom ≫
          (Scheme.Modules.pushforward i).map (tensorSheafFunctorObjSelf π F).hom =
      (Scheme.Modules.pullbackPushforwardAdjunction i).unit.app F' ≫
        (Scheme.Modules.pushforward i).map e.hom :=
  (comp_eq_of_thirdMap_factors
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(X'.toRingedSpace).presheaf, (X'.toRingedSpace).IsSheaf⟩))
      (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨(X.toRingedSpace).presheaf, (X.toRingedSpace).IsSheaf⟩))
      (Scheme.Modules.pushforward i) _ _ _ _ _ _ _ _ _ e.hom _ _ _ _ _ _ _
      ((eqToHom_trans _ _).trans (eqToHom_refl _ _))
      ((eqToHom_trans _ _).trans (eqToHom_refl _ _))
      (tensorSheafFunctorObjSelf_inv_eq π' F')
      (tensorSheafFunctor_map_eq_eqToHom π' F' (quotCoeff φ))
      (pushforwardTensorSheafIsoGen_hom φ π' π i hsq F' F e (ModuleCat.of A A))
      (eqToHom_comp_tensorSheafFunctorObjSelf_hom π F)
      (thirdMapUnit φ π' π i hsq) rfl).trans
    (unit_comp_eq_tensorProjectionFormula φ π' π i hsq F' F e).symm

end ThirdMapGen

/-! ### Lifting sections along the third map -/

section Sections

/-- A morphism of modules commutes with the restriction maps of sections. -/
theorem modulesHom_app_presheaf_map {Y : Scheme.{u}} {M N : Y.Modules} (φ : M ⟶ N)
    {U V : Y.Opens} (h : U ⟶ V) (s : Γ(M, V)) :
    φ.app U (M.presheaf.map h.op s) = N.presheaf.map h.op (φ.app V s) :=
  ConcreteCategory.congr_hom (φ.mapPresheaf.naturality h.op) s

/-- On sections, the inverse of an isomorphism of modules undoes the isomorphism. -/
theorem modulesIso_inv_app_hom_app {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    (U : Y.Opens) (s : Γ(M, U)) : e.inv.app U (e.hom.app U s) = s := by
  rw [← CategoryTheory.comp_apply, ← Scheme.Modules.Hom.comp_app, e.hom_inv_id,
    Scheme.Modules.Hom.id_app, CategoryTheory.id_apply]

/-- On sections, an isomorphism of modules undoes its inverse. -/
theorem modulesIso_hom_app_inv_app {Y : Scheme.{u}} {M N : Y.Modules} (e : M ≅ N)
    (U : Y.Opens) (s : Γ(N, U)) : e.hom.app U (e.inv.app U s) = s :=
  modulesIso_inv_app_hom_app e.symm U s

variable {X X' : Scheme.{u}} (i : X ⟶ X')

/-- `pushforwardSection` is natural in the module. -/
theorem pushforwardSection_naturality {G G' : X.Modules} (φ : G ⟶ G') (s : Γ(G, ⊤)) :
    ((Scheme.Modules.pushforward i).map φ).app ⊤ (pushforwardSection i G s) =
      pushforwardSection i G' (φ.app ⊤ s) :=
  modulesHom_app_presheaf_map φ (homOfLE le_top) s

/-- Restricting a section read on `i_* G` back to `⊤` gives the section back. -/
theorem presheaf_map_pushforwardSection (G : X.Modules) (s : Γ(G, ⊤)) :
    G.presheaf.map (eqToHom (show (⊤ : X.Opens) = i ⁻¹ᵁ ⊤ by simp)).op
      (pushforwardSection i G s) = s :=
  ConcreteCategory.congr_hom
    ((G.presheaf.map_comp (homOfLE le_top : i ⁻¹ᵁ ⊤ ⟶ ⊤).op
      (eqToHom (show (⊤ : X.Opens) = i ⁻¹ᵁ ⊤ by simp)).op).symm.trans
        (G.presheaf.map_id (op ⊤))) s

/-- Reading a section of `G` over `i⁻¹ ⊤` back on `i_* G` gives the section back. -/
theorem pushforwardSection_presheaf_map (G : X.Modules) (s : Γ(G, i ⁻¹ᵁ ⊤)) :
    pushforwardSection i G
      (G.presheaf.map (eqToHom (show (⊤ : X.Opens) = i ⁻¹ᵁ ⊤ by simp)).op s) = s :=
  ConcreteCategory.congr_hom
    ((G.presheaf.map_comp (eqToHom (show (⊤ : X.Opens) = i ⁻¹ᵁ ⊤ by simp)).op
      (homOfLE le_top : i ⁻¹ᵁ ⊤ ⟶ ⊤).op).symm.trans
        (G.presheaf.map_id (op (i ⁻¹ᵁ ⊤)))) s

/-- **Lifting a section along a composite that is a morphism `κ : 𝓕' ⟶ i_* 𝓕`.** If `κ` is
the composite of an isomorphism `ι`, a morphism `m`, and the isomorphisms `p` and `i_* σ`, then a
section `x` of `𝓕`, read through `σ⁻¹` and `p⁻¹`, is in the image of `m` on global sections
exactly when it is the restriction of the image under `κ` of a global section of `𝓕'`. -/
theorem exists_section_iff_of_comp_eq {F' Z Z₃ : X'.Modules} {T F : X.Modules} (ι : Z ≅ F')
    (m : Z ⟶ Z₃) (p : Z₃ ≅ (Scheme.Modules.pushforward i).obj T) (σ : T ≅ F)
    (κ : F' ⟶ (Scheme.Modules.pushforward i).obj F)
    (hκ : ι.inv ≫ m ≫ p.hom ≫ (Scheme.Modules.pushforward i).map σ.hom = κ) (x : Γ(F, ⊤)) :
    (∃ y : Γ(Z, ⊤), m.app ⊤ y = p.inv.app ⊤ (pushforwardSection i T (σ.inv.app ⊤ x))) ↔
      ∃ y : Γ(F', ⊤),
        F.presheaf.map (eqToHom (show (⊤ : X.Opens) = i ⁻¹ᵁ ⊤ by simp)).op (κ.app ⊤ y) = x := by
  have hκy : ∀ y : Γ(F', ⊤), κ.app ⊤ y =
      ((Scheme.Modules.pushforward i).map σ.hom).app ⊤ (p.hom.app ⊤ (m.app ⊤ (ι.inv.app ⊤ y))) :=
    fun y => by rw [← hκ]; rfl
  have hσx : ((Scheme.Modules.pushforward i).map σ.hom).app ⊤
      (pushforwardSection i T (σ.inv.app ⊤ x)) = pushforwardSection i F x := by
    rw [pushforwardSection_naturality, modulesIso_hom_app_inv_app]
  constructor
  · rintro ⟨y, hy⟩
    refine ⟨ι.hom.app ⊤ y, ?_⟩
    rw [hκy, modulesIso_inv_app_hom_app, hy, modulesIso_hom_app_inv_app, hσx,
      presheaf_map_pushforwardSection]
  · rintro ⟨y, hy⟩
    refine ⟨ι.inv.app ⊤ y, ?_⟩
    have h₁ : κ.app ⊤ y = pushforwardSection i F x :=
      (pushforwardSection_presheaf_map i F (κ.app ⊤ y)).symm.trans (congrArg _ hy)
    have h₂ : p.hom.app ⊤ (m.app ⊤ (ι.inv.app ⊤ y)) =
        pushforwardSection i T (σ.inv.app ⊤ x) :=
      (modulesIso_inv_app_hom_app ((Scheme.Modules.pushforward i).mapIso σ) ⊤ _).symm.trans
        ((congrArg (((Scheme.Modules.pushforward i).map σ.inv).app ⊤)
          ((hκy y).symm.trans h₁)).trans (pushforwardSection_naturality i σ.inv x))
    rw [← h₂, modulesIso_inv_app_hom_app]

end Sections

/-! ### Condition (iii): the boundary vanishes exactly when the section lifts -/

/-- `reductionMapGen` is the unit followed by the direct image of `baseChangeSheafIsoGen`. -/
theorem reductionMapGen_eq_unit_comp {W X X₁ : Scheme.{u}} (s : X ⟶ W) (s₁ : X₁ ⟶ W)
    (𝓕 : W.Modules) (g : X₁ ⟶ X) (hsnd : g ≫ s = s₁) :
    reductionMapGen s s₁ 𝓕 g hsnd =
      (Scheme.Modules.pullbackPushforwardAdjunction g).unit.app
          ((Scheme.Modules.pullback s).obj 𝓕) ≫
        (Scheme.Modules.pushforward g).map (baseChangeSheafIsoGen s s₁ 𝓕 g hsnd).hom :=
  rfl

/-! ### The lifting criterion at a base-change square -/

section Core

variable {S : Scheme.{u}} {A' A : CommRingCat.{u}} (t : Spec A' ⟶ S) (t' : Spec A ⟶ S)
  (α : Over.mk t' ⟶ Over.mk t) (φ : A' ⟶ A) {W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)
  [𝓕.IsQuasicoherent]

/-- **The lifting criterion at the base-change square of `α : T' → T`**, for `α` with
underlying morphism `Spec φ` whose base change is a closed immersion: a section `x` of `𝓕_{T'}`,
read on `W_T` as a section of `𝓕_T ⊗_{A'} A`, is the image of a section of `𝓕_T ⊗_{A'} A'` under
the map induced by `φ` exactly when `x` is the restriction of a section of `𝓕_T`. -/
theorem exists_preimage_iff_exists_restriction (hα : α.left = Spec.map φ)
    (hi : IsClosedImmersion (baseChangeMap q α))
    (x : Γ((Scheme.Modules.pullback (pullback.snd (Over.mk t').hom q)).obj 𝓕, ⊤)) :
    (∃ y : Γ((tensorSheafFunctor (pullback.fst (Over.mk t).hom q)
          ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)).obj
            (ModuleCat.of A' A'), ⊤),
        Scheme.Modules.Hom.app ((tensorSheafFunctor (pullback.fst (Over.mk t).hom q)
          ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)).map
            (quotCoeff φ)) ⊤ y =
        Scheme.Modules.Hom.app (@pushforwardTensorSheafIsoGen _ _ φ _ _
          (pullback.fst (Over.mk t).hom q) (pullback.fst (Over.mk t').hom q) (baseChangeMap q α)
          (isPullback_baseChangeMap_of_eq t t' α φ q hα)
          ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)
          ((Scheme.Modules.pullback (pullback.snd (Over.mk t').hom q)).obj 𝓕)
          (baseChangeSheafIsoGen _ _ 𝓕 (baseChangeMap q α) (baseChangeMap_comp_snd q α)) hi
          (ModuleCat.of A A)).inv ⊤
          (pushforwardSection (baseChangeMap q α) _
            (Scheme.Modules.Hom.app (tensorSheafFunctorObjSelf (pullback.fst (Over.mk t').hom q)
              ((Scheme.Modules.pullback (pullback.snd (Over.mk t').hom q)).obj 𝓕)).inv ⊤ x))) ↔
      ∃ y : Γ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕, ⊤),
        (sectionsPresheafOver q 𝓕).map α.op y = x := by
  refine (exists_section_iff_of_comp_eq (baseChangeMap q α)
    (tensorSheafFunctorObjSelf (pullback.fst (Over.mk t).hom q)
      ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)) _ _
    (tensorSheafFunctorObjSelf (pullback.fst (Over.mk t').hom q)
      ((Scheme.Modules.pullback (pullback.snd (Over.mk t').hom q)).obj 𝓕)) _
    (@thirdMap_eq _ _ φ _ _ (pullback.fst (Over.mk t).hom q) (pullback.fst (Over.mk t').hom q)
      (baseChangeMap q α) (isPullback_baseChangeMap_of_eq t t' α φ q hα)
      ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)
      ((Scheme.Modules.pullback (pullback.snd (Over.mk t').hom q)).obj 𝓕)
      (baseChangeSheafIsoGen _ _ 𝓕 (baseChangeMap q α) (baseChangeMap_comp_snd q α)) hi)
    x).trans ?_
  refine exists_congr fun y => ?_
  rw [sectionsPresheafOver_map_eq_reductionMapGen, reductionMapGen_eq_unit_comp]
  rfl

/-- `exists_preimage_iff_exists_restriction` with the sections of `𝓕_T ⊗_{A'} A'` read as the
`A'`-module `H⁰(W_T, -)`, the spelling of `exists_section_iff_obstructionClass_eq_zero`. -/
theorem exists_preimage_iff_exists_restriction' (hα : α.left = Spec.map φ)
    (hi : IsClosedImmersion (baseChangeMap q α))
    (x : Γ((Scheme.Modules.pullback (pullback.snd (Over.mk t').hom q)).obj 𝓕, ⊤)) :
    (∃ y : ((sectionsOverBase (pullback.fst (Over.mk t).hom q)).obj
          ((tensorSheafFunctor (pullback.fst (Over.mk t).hom q)
            ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)).obj
              (ModuleCat.of A' A')) : Type u),
        (sectionsOverBase (pullback.fst (Over.mk t).hom q)).map
          ((tensorSheafFunctor (pullback.fst (Over.mk t).hom q)
            ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)).map
              (quotCoeff φ)) y =
        Scheme.Modules.Hom.app (@pushforwardTensorSheafIsoGen _ _ φ _ _
          (pullback.fst (Over.mk t).hom q) (pullback.fst (Over.mk t').hom q) (baseChangeMap q α)
          (isPullback_baseChangeMap_of_eq t t' α φ q hα)
          ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕)
          ((Scheme.Modules.pullback (pullback.snd (Over.mk t').hom q)).obj 𝓕)
          (baseChangeSheafIsoGen _ _ 𝓕 (baseChangeMap q α) (baseChangeMap_comp_snd q α)) hi
          (ModuleCat.of A A)).inv ⊤
          (pushforwardSection (baseChangeMap q α) _
            (Scheme.Modules.Hom.app (tensorSheafFunctorObjSelf (pullback.fst (Over.mk t').hom q)
              ((Scheme.Modules.pullback (pullback.snd (Over.mk t').hom q)).obj 𝓕)).inv ⊤ x))) ↔
      ∃ y : Γ((Scheme.Modules.pullback (pullback.snd (Over.mk t).hom q)).obj 𝓕, ⊤),
        (sectionsPresheafOver q 𝓕).map α.op y = x :=
  exists_preimage_iff_exists_restriction t t' α φ q 𝓕 hα hi x

/-- `exists_preimage_iff_exists_restriction'` in the spelling of `topProj`, `topSheaf` and
`sectionTransportOver`. -/
theorem exists_preimage_iff_exists_restriction_top (hα : α.left = Spec.map φ)
    (hi : IsClosedImmersion (baseChangeMap q α)) (x : Γ(topSheaf t' q 𝓕, ⊤)) :
    (∃ y : ((sectionsOverBase (topProj t q)).obj
          ((tensorSheafFunctor (topProj t q) (topSheaf t q 𝓕)).obj (ModuleCat.of A' A')) :
            Type u),
        (sectionsOverBase (topProj t q)).map
          ((tensorSheafFunctor (topProj t q) (topSheaf t q 𝓕)).map (quotCoeff φ)) y =
        sectionTransportOver t t' α φ q 𝓕 hα hi x) ↔
      ∃ y : Γ(topSheaf t q 𝓕, ⊤), (sectionsPresheafOver q 𝓕).map α.op y = x := by
  unfold sectionTransportOver
  rw [pushforwardTensorSheafIsoOver_eq]
  exact exists_preimage_iff_exists_restriction' t t' α φ q 𝓕 hα hi x

end Core

section Lift

attribute [local instance] HasDerivedCategory.standard

variable {B : BigFppfSite.{u}} {Λ : Type u} [CommRing Λ] {hS : B.Contains (Spec (.of Λ))}
  {a : SiteAlgebra B (Spec (.of Λ)) hS} {W : Scheme.{u}} (g : W ⟶ Spec (.of Λ)) (F : W.Modules)
  [F.IsQuasicoherent]

/-- **Condition (iii) of Stacks 07YG for the example of Stacks 07YH.** The boundary of a section
`x` of `𝓕_A`, computed on `W_{A'}`, vanishes exactly when `x` is the restriction of a section of
`𝓕_{A'}` along `W_A → W_{A'}`, that is, exactly when `x` is in the image of the restriction map
`F(A') → F(A)` of the functor of sections. -/
theorem thickeningClass_eq_zero_iff (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F)
    (t : DeformationSituation B (Spec (.of Λ)) hS a) (x : Γ(topSheaf a.toScheme g F, ⊤)) :
    thickeningClass g F hF t x = 0 ↔
      ∃ y : Γ(topSheaf t.top.toScheme g F, ⊤),
        (sectionsPresheafOver g F).map (thickeningOver t).op y = x := by
  unfold thickeningClass
  rw [iso_hom_eq_zero_iff]
  unfold thickeningSection
  refine (exists_section_iff_obstructionClass_eq_zero (topProj t.top.toScheme g)
    (topSheaf t.top.toScheme g F) (isFlatOver_topSheaf g F hF t.top.toScheme)
    (kernelShortComplex_shortExact t) _).symm.trans ?_
  exact exists_preimage_iff_exists_restriction_top t.top.toScheme a.toScheme (thickeningOver t)
    (CommRingCat.ofHom t.hom.ringMap) g F (thickeningOver_left t)
    (isClosedImmersion_thickening g t) x

end Lift

end Deformation.Artin.SectionsSheaf

end
