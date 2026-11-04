module

public import StacksFrontier.Deformation.Artin.Obstruction.SectionsWComparison

/-!
# The obstruction theory of Stacks 07YH

Let `S = Spec Λ`, let `g : W → S` be a morphism of schemes and let `𝓕` be a quasi-coherent
`𝒪_W`-module, flat over `S`. The category fibred in groupoids `𝒳` attached to the functor
`T/S ↦ H⁰(W_T, 𝓕_T)` has an obstruction theory in the sense of Stacks 07YG: at an object `x` of
`𝒳` over `Spec A` the obstruction modules are `𝒪_x(M) = H¹(W_A, 𝓕_A ⊗_A M)`, and the obstruction
element of a deformation situation `(x, A' → A)` with kernel `I` is the image of `x` under the
boundary map `H⁰(W_A, 𝓕_A) → H¹(W_A, 𝓕_A ⊗_A I)` of the short exact sequence
`0 → 𝓕_A ⊗_A I → 𝓕_{A'} → 𝓕_A → 0`. No hypothesis on `W` beyond being a scheme over `S` is
needed.

All the maps between obstruction modules at different bases are computed on the single scheme
`W`. For an affine scheme `Spec A → Spec Λ` the projection `p : W_A → W` is affine, so
`H¹(W_A, 𝓕_A ⊗_A M) = H¹(W, p_*(𝓕_A ⊗_A M)) = H¹(W, 𝓕 ⊗_Λ M)` (`wComparison`). A morphism
`(x, A) → (y, A₁)` of objects together with an `A`-linear map `M → N` into an `A₁`-module is in
particular a `Λ`-linear map `M → N`, which induces `H¹(W, 𝓕 ⊗_Λ M) → H¹(W, 𝓕 ⊗_Λ N)`; read
through the two comparisons this is the map of obstruction modules of clause (2). Since neither
`W` nor the coefficient functor `𝓕 ⊗_Λ -` depends on the base, the identity and composition laws
of condition (i) are functor laws, and `A`-linearity is the `A`-linearity of
`M ↦ H¹(W_A, 𝓕_A ⊗_A M)` together with the naturality of the comparison in `M`.

Under the same comparison the obstruction element becomes the boundary, on `W`, of the class of
the section named by `x` for the short exact sequence `𝓕 ⊗_Λ (0 → I → A' → A → 0)`
(`wComparison_sectionsObstructionClass`). A morphism of deformation situations is a morphism of
these short exact sequences of `Λ`-modules, so condition (ii) is the naturality of the boundary
map of the cohomology of `W` in the short exact sequence, together with the compatibility of the
sections named by the two objects (`wComparison_naturality_section`). Condition (iii) is
`thickeningClass_eq_zero_iff`: the obstruction element vanishes exactly when the section named by
`x` is the restriction of a section over `A'`, which is what a lift of `x` to `Spec A'` is.

## Main definitions

* `Deformation.Artin.DeformationSituation.kernelMap` — the map of kernels induced by a
  morphism of square-zero surjections.
* `Deformation.Artin.SectionsSheaf.restrictScalarsHomOfLinearMap` — a map `M → N` from an
  `A`-module to an `A₁`-module, linear along a ring map `A → A₁` under `Λ`, as a map of
  `Λ`-modules.
* `Deformation.Artin.SectionsSheaf.wComparisonMap` — the map
  `|Hⁿ(W_A, 𝓕_A ⊗_A M)| → |Hⁿ(W_{A₁}, 𝓕_{A₁} ⊗_{A₁} N)|` induced by a `Λ`-linear map `M → N`,
  computed on `W`.
* `Deformation.Artin.SectionsSheaf.wObstructionMap` — the same map in degree one, as a map of
  obstruction modules, linear along `A → A₁`; `affineWObstructionMap` is the same map at a
  morphism of affine objects.
* `Deformation.Artin.SectionsSheaf.kernelShortComplexΛHom` — the morphism of the sequences
  `0 → I → A' → A → 0` over `Λ` induced by a morphism of deformation situations.
* `Deformation.Artin.SectionsSheaf.sectionsObstructionTheory` — **the obstruction theory of
  Stacks 07YH**, as a `Deformation.Artin.ObstructionTheory`.

## Main results

* `Deformation.Artin.SectionsSheaf.wComparisonMap_id`, `wComparisonMap_comp` and
  `wComparisonMap_restrictScalars_map` — the maps computed on `W` are functorial, and at a
  fixed base they are the maps of the cohomology functor.
* `Deformation.Artin.SectionsSheaf.affineWObstructionMap_id_apply` and
  `affineWObstructionMap_comp_apply` — condition (i) and the compatibility with the local
  obstruction functors.
* `Deformation.Artin.SectionsSheaf.affineWObstructionMap_sectionsObstructionClass` —
  **condition (ii)**: the map of obstruction modules induced by a morphism of deformation
  situations carries the obstruction element to the obstruction element.
* `Deformation.Artin.SectionsSheaf.hasLift_iff_thickeningClass_eq_zero` — an object lifts across
  a deformation situation iff the boundary of the section it names vanishes.
* `Deformation.Artin.SectionsSheaf.hasLift_iff_sectionsObstructionClass_eq_zero` — **condition
  (iii)**: an object lifts across a deformation situation iff its obstruction element vanishes.
* `Deformation.Artin.SectionsSheaf.exists_obstructionTheory` — **Stacks 07YH**.

## Implementation notes

The map of obstruction modules of clause (2) is defined through `W`, not through the base change
morphism `W_{A₁} → W_A`: clause (2) asks for an induced map satisfying the coherence conditions,
and on `W` these conditions hold by functoriality alone, with no compatibility between the base
changes along different ring maps to check.

The lifting criterion of the category of elements is stated with the functor of sections on the
site, `sectionsPresheaf`, and the vanishing criterion of the boundary with the functor on all
schemes over `S`, `sectionsPresheafOver`, along `thickeningOver`. The two restriction maps are
equal by unfolding, but the kernel checks this cheaply only when the restriction maps are
compared as morphisms, with the objects they are applied at spelled alike; comparing them on
elements makes it normalise the restriction maps themselves. `hasLift_iff_thickeningClass_eq_zero`
therefore passes from one to the other through `exists_sectionsPresheaf_map_eq_iff` and
`exists_map_apply_eq_iff_of_heq`, and is stated for the category of elements in the spelling of
`hasLift_iff_exists_section_sectionsPresheaf`. For the same reason the element-wise identities
between maps of cohomology groups are proved with those maps generalised to variables.

The naturality square of the connecting map in
`affineWObstructionMap_sectionsObstructionClass` obeys the same discipline. The target of
`(abCohomology g).δ` is `Hⁿ⁺¹` of `((kernelShortComplexΛ s).map (tensorSheafFunctor g F)).X₁`,
while the arrow composed after it is `Hⁿ⁺¹` of a `tensorSheafFunctor`-image; the two objects agree
by unfolding `ShortComplex.map`, but letting the composition propagate its expected type into the
implicit source of `CategoryTheory.Functor.map` makes the elaborator normalise
`tensorSheafFunctor g F` instead. That source is therefore given explicitly at each such
composition, and the morphism between the two mapped sequences is
`CategoryTheory.Functor.mapShortComplex.map` rather than a `ShortComplex.Hom` rebuilt from its
components, which would raise the same comparison once per field.

The source's standing hypothesis that `Λ` is Noetherian is carried by `exists_obstructionTheory`,
as in the source, but is not used by the construction.

## References

* [Stacks Project, Tag 07YH](https://stacks.math.columbia.edu/tag/07YH)
* [Stacks Project, Tag 07YG](https://stacks.math.columbia.edu/tag/07YG)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

universe u

/-! ### The map of kernels of a morphism of square-zero surjections -/

namespace Deformation.Artin.DeformationSituation

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- The ring map `A' → A₁'` of a commutative square of ring maps between two deformation
situations carries the kernel `I` of `A' → A` into the kernel `I₁` of `A₁' → A₁`. -/
theorem map_kernelVal_mem_ker {a b : SiteAlgebra B S hS} (s : DeformationSituation B S hS a)
    (t : DeformationSituation B S hS b) (ψ : a.carrier →+* b.carrier)
    (ψ' : s.top.carrier →+* t.top.carrier)
    (comm : t.hom.ringMap.comp ψ' = ψ.comp s.hom.ringMap) (z : (s.kernelObj : Type u)) :
    ψ' (s.kernelVal z) ∈ RingHom.ker t.hom.ringMap := by
  have hz : s.hom.ringMap (s.kernelVal z) = 0 := RingHom.mem_ker.mp z.2
  exact RingHom.mem_ker.mpr ((RingHom.congr_fun comm (s.kernelVal z)).trans
    (by rw [RingHom.comp_apply, hz, map_zero]))

/-- **The map of kernels of a morphism of deformation situations.** For deformation situations
`A' → A` and `A₁' → A₁` with kernels `I` and `I₁`, and ring maps `ψ : A → A₁` and
`ψ' : A' → A₁'` forming a commutative square, the restriction `I → I₁` of `ψ'`; it is `A`-linear
when `I₁` is regarded as an `A`-module along `ψ`. -/
def kernelMap {a b : SiteAlgebra B S hS} (s : DeformationSituation B S hS a)
    (t : DeformationSituation B S hS b) (ψ : a.carrier →+* b.carrier)
    (ψ' : s.top.carrier →+* t.top.carrier)
    (comm : t.hom.ringMap.comp ψ' = ψ.comp s.hom.ringMap) :
    letI : Module a.carrier (t.kernelObj : Type u) := Module.compHom _ ψ
    (s.kernelObj : Type u) →ₗ[a.carrier] (t.kernelObj : Type u) :=
  letI : Module a.carrier (t.kernelObj : Type u) := Module.compHom _ ψ
  { toFun := fun z => ⟨ψ' (s.kernelVal z), map_kernelVal_mem_ker s t ψ ψ' comm z⟩
    map_add' := fun z₁ z₂ => Subtype.ext (map_add ψ' (s.kernelVal z₁) (s.kernelVal z₂))
    map_smul' := fun r z => by
      obtain ⟨r', rfl⟩ := s.surjective r
      have hs : s.kernelVal (s.hom.ringMap r' • z) = r' * s.kernelVal z :=
        letI := s.kernelModule
        congrArg Subtype.val (Stacks.Smooth.kerModule_smul s.surjective s.sq_eq_bot r' z)
      have hr : ψ (s.hom.ringMap r') = t.hom.ringMap (ψ' r') :=
        (RingHom.congr_fun comm r').symm
      have ht : ∀ w : (t.kernelObj : Type u),
          t.kernelVal (t.hom.ringMap (ψ' r') • w) = ψ' r' * t.kernelVal w := fun w =>
        letI := t.kernelModule
        congrArg Subtype.val (Stacks.Smooth.kerModule_smul t.surjective t.sq_eq_bot (ψ' r') w)
      apply Subtype.ext
      refine (congrArg ψ' hs).trans ((map_mul ψ' _ _).trans ?_)
      refine Eq.trans ?_ (congrArg (fun c : b.carrier => t.kernelVal (c • _)) hr.symm)
      exact (ht ⟨ψ' (s.kernelVal z), map_kernelVal_mem_ker s t ψ ψ' comm z⟩).symm }

/-- `kernelMap` is the ring map `A' → A₁'` on the underlying elements of `A'`. -/
@[simp]
theorem kernelVal_kernelMap {a b : SiteAlgebra B S hS} (s : DeformationSituation B S hS a)
    (t : DeformationSituation B S hS b) (ψ : a.carrier →+* b.carrier)
    (ψ' : s.top.carrier →+* t.top.carrier)
    (comm : t.hom.ringMap.comp ψ' = ψ.comp s.hom.ringMap) (z : (s.kernelObj : Type u)) :
    t.kernelVal (kernelMap s t ψ ψ' comm z) = ψ' (s.kernelVal z) :=
  rfl

end Deformation.Artin.DeformationSituation

namespace Deformation.Artin.SectionsSheaf

/-! ### Semilinear maps as maps of `Λ`-modules -/

section RestrictScalars

variable {Λ A A' : CommRingCat.{u}} {φ : Λ ⟶ A} {φ' : Λ ⟶ A'}

/-- **A semilinear map, as a map of `Λ`-modules.** For a ring map `ψ : A ⟶ A'` under `Λ`, a map
`f : M → N` from an `A`-module to an `A'`-module which is `A`-linear for the structure of
`A`-module on `N` along `ψ` is `Λ`-linear when `M` and `N` are regarded as `Λ`-modules along
`Λ → A` and `Λ → A'`. -/
def restrictScalarsHomOfLinearMap (ψ : A ⟶ A') (hψ : φ ≫ ψ = φ') {M : ModuleCat.{u} A}
    {N : ModuleCat.{u} A'}
    (f : letI : Module A (N : Type u) := Module.compHom _ ψ.hom
      (M : Type u) →ₗ[A] (N : Type u)) :
    (ModuleCat.restrictScalars φ.hom).obj M ⟶ (ModuleCat.restrictScalars φ'.hom).obj N :=
  letI : Module A (N : Type u) := Module.compHom _ ψ.hom
  ModuleCat.ofHom (X := (ModuleCat.restrictScalars φ.hom).obj M)
    (Y := (ModuleCat.restrictScalars φ'.hom).obj N)
    { toFun := f
      map_add' := f.map_add
      map_smul' := fun r m => by
        subst hψ
        exact f.map_smul (φ.hom r) m }

/-- `restrictScalarsHomOfLinearMap` is the given map on elements. -/
@[simp]
theorem restrictScalarsHomOfLinearMap_apply (ψ : A ⟶ A') (hψ : φ ≫ ψ = φ')
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} A'}
    (f : letI : Module A (N : Type u) := Module.compHom _ ψ.hom
      (M : Type u) →ₗ[A] (N : Type u)) (m : (M : Type u)) :
    (restrictScalarsHomOfLinearMap ψ hψ f).hom m = f m :=
  rfl

end RestrictScalars

variable {Λ : Type u} [CommRing Λ] (B : BigFppfSite.{u}) (hS : B.Contains (Spec (.of Λ)))
  {W : Scheme.{u}} (g : W ⟶ Spec (.of Λ)) (F : W.Modules) [F.IsQuasicoherent]

/-! ### The maps of cohomology groups between bases, computed on `W` -/

section ComparisonMap

variable {A A' A'' : CommRingCat.{u}} (t : Spec A ⟶ Spec (.of Λ)) (t' : Spec A' ⟶ Spec (.of Λ))
  (t'' : Spec A'' ⟶ Spec (.of Λ)) (n : ℕ)

/-- **The map of cohomology groups between two bases induced by a `Λ`-linear map, computed on
`W`.** For affine schemes `t : Spec A → Spec Λ` and `t' : Spec A' → Spec Λ`, an `A`-module `M`,
an `A'`-module `N` and a `Λ`-linear map `f : M → N`, the map
`|Hⁿ(W_A, 𝓕_A ⊗_A M)| → |Hⁿ(W_{A'}, 𝓕_{A'} ⊗_{A'} N)|` which, read on `W` through
`wComparison`, is `|Hⁿ(W, 𝓕 ⊗_Λ f)|`. -/
def wComparisonMap {M : ModuleCat.{u} A} {N : ModuleCat.{u} A'}
    (f : (ModuleCat.restrictScalars (Spec.preimage t).hom).obj M ⟶
      (ModuleCat.restrictScalars (Spec.preimage t').hom).obj N) :
    ((abCohomology (topProj t g)).functor n).obj
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) ⟶
      ((abCohomology (topProj t' g)).functor n).obj
        ((tensorSheafFunctor (topProj t' g) (topSheaf t' g F)).obj N) :=
  (wComparison g F t n).hom.app M ≫
    ((abCohomology g).functor n).map ((tensorSheafFunctor g F).map f) ≫
      (wComparison g F t' n).inv.app N

/-- `wComparisonMap` along the identity is the identity. -/
@[simp]
theorem wComparisonMap_id (M : ModuleCat.{u} A) :
    wComparisonMap g F t t n (𝟙 ((ModuleCat.restrictScalars (Spec.preimage t).hom).obj M)) =
      𝟙 _ := by
  simp [wComparisonMap]

/-- `wComparisonMap` along a composite is the composite. -/
theorem wComparisonMap_comp {M : ModuleCat.{u} A} {N : ModuleCat.{u} A'}
    {L : ModuleCat.{u} A''}
    (f : (ModuleCat.restrictScalars (Spec.preimage t).hom).obj M ⟶
      (ModuleCat.restrictScalars (Spec.preimage t').hom).obj N)
    (f' : (ModuleCat.restrictScalars (Spec.preimage t').hom).obj N ⟶
      (ModuleCat.restrictScalars (Spec.preimage t'').hom).obj L) :
    wComparisonMap g F t t'' n (f ≫ f') =
      wComparisonMap g F t t' n f ≫ wComparisonMap g F t' t'' n f' := by
  simp [wComparisonMap]

/-- **At a fixed base, `wComparisonMap` is the map of the cohomology functor**: along the
restriction of scalars of an `A`-linear map `f : M → N` it is `|Hⁿ(W_A, 𝓕_A ⊗_A f)|`. This is
the naturality of `wComparison`. -/
theorem wComparisonMap_restrictScalars_map {M N : ModuleCat.{u} A} (f : M ⟶ N) :
    wComparisonMap g F t t n ((ModuleCat.restrictScalars (Spec.preimage t).hom).map f) =
      ((abCohomology (topProj t g)).functor n).map
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).map f) := by
  have h := (wComparison g F t n).hom.naturality f
  simp only [Functor.comp_map] at h
  rw [wComparisonMap, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id_app,
    Category.comp_id]

/-- `wComparisonMap_restrictScalars_map`, for a `Λ`-linear map given as an `A`-linear map on
elements. -/
theorem wComparisonMap_eq_map {M N : ModuleCat.{u} A} (f : M ⟶ N)
    (f' : (ModuleCat.restrictScalars (Spec.preimage t).hom).obj M ⟶
      (ModuleCat.restrictScalars (Spec.preimage t).hom).obj N)
    (h : ∀ m : (M : Type u), f' m = f m) :
    wComparisonMap g F t t n f' =
      ((abCohomology (topProj t g)).functor n).map
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).map f) := by
  have e : f' = (ModuleCat.restrictScalars (Spec.preimage t).hom).map f := by
    ext m
    exact h m
  rw [e, wComparisonMap_restrictScalars_map]

/-- **`wComparisonMap` read on `W`**: under `wComparison`, it is the map
`|Hⁿ(W, 𝓕 ⊗_Λ M)| → |Hⁿ(W, 𝓕 ⊗_Λ N)|` induced by the `Λ`-linear map. -/
theorem wComparisonMap_apply_eq_iff {M : ModuleCat.{u} A} {N : ModuleCat.{u} A'}
    (f : (ModuleCat.restrictScalars (Spec.preimage t).hom).obj M ⟶
      (ModuleCat.restrictScalars (Spec.preimage t').hom).obj N)
    (o : (((abCohomology (topProj t g)).functor n).obj
      ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).obj M) : Type u))
    (o' : (((abCohomology (topProj t' g)).functor n).obj
      ((tensorSheafFunctor (topProj t' g) (topSheaf t' g F)).obj N) : Type u)) :
    wComparisonMap g F t t' n f o = o' ↔
      ((abCohomology g).functor n).map ((tensorSheafFunctor g F).map f)
          ((wComparison g F t n).hom.app M o) =
        (wComparison g F t' n).hom.app N o' := by
  rw [wComparisonMap, CategoryTheory.comp_apply, CategoryTheory.comp_apply]
  constructor
  · rintro rfl
    exact (((wComparison g F t' n).app N).inv_hom_id_apply _).symm
  · intro h
    rw [h]
    exact ((wComparison g F t' n).app N).hom_inv_id_apply o'

end ComparisonMap

/-! ### The map of obstruction modules -/

section ObstructionMap

variable {A A' : CommRingCat.{u}} (t : Spec A ⟶ Spec (.of Λ)) (t' : Spec A' ⟶ Spec (.of Λ))

/-- Forgetting the module structure does not change a linear map on elements. -/
theorem forget₂_addCommGrpCat_map_apply {R : Type u} [Ring R] {X Y : ModuleCat.{u} R}
    (f : X ⟶ Y) (x : (X : Type u)) :
    (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map f x = f x :=
  rfl

/-- The map of `|H¹(X, -)|` on `𝓕 ⊗_R f` is the map of the obstruction functor along `f`, with
the module structures forgotten. -/
theorem abCohomology_map_tensorSheafFunctor_map {R : CommRingCat.{u}} {X : Scheme.{u}}
    (π : X ⟶ Spec R) (G : SheafOfModules.{u} X.ringCatSheaf) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) :
    ((abCohomology π).functor 1).map ((tensorSheafFunctor π G).map f) =
      (forget₂ (ModuleCat.{u} R) AddCommGrpCat.{u}).map ((obstructionFunctor π G).map f) :=
  rfl

/-- `abCohomology_map_tensorSheafFunctor_map`, on elements. -/
theorem abCohomology_map_tensorSheafFunctor_map_apply {R : CommRingCat.{u}} {X : Scheme.{u}}
    (π : X ⟶ Spec R) (G : SheafOfModules.{u} X.ringCatSheaf) {M N : ModuleCat.{u} R}
    (f : M ⟶ N) (o : ((obstructionFunctor π G).obj M : Type u)) :
    ((abCohomology π).functor 1).map ((tensorSheafFunctor π G).map f) o =
      (obstructionFunctor π G).map f o :=
  (ConcreteCategory.congr_hom (abCohomology_map_tensorSheafFunctor_map π G f) o).trans
    (forget₂_addCommGrpCat_map_apply _ o)

/-- Two composites of morphisms of abelian groups that agree agree on elements. -/
theorem apply_eq_of_comp_eq {X Y Z V : AddCommGrpCat.{u}} {a : X ⟶ Y} {b : Y ⟶ V} {c : X ⟶ Z}
    {d : Z ⟶ V} (h : a ≫ b = c ≫ d) (x : (X : Type u)) : b (a x) = d (c x) := by
  rw [← CategoryTheory.comp_apply, h, CategoryTheory.comp_apply]

/-- A morphism of abelian groups which is a composite is the composite on elements. -/
theorem apply_eq_apply_of_eq_comp {X Y Z : AddCommGrpCat.{u}} {f : X ⟶ Z} {a : X ⟶ Y}
    {b : Y ⟶ Z} (h : f = a ≫ b) (x : (X : Type u)) : f x = b (a x) := by
  rw [h, CategoryTheory.comp_apply]

/-- Two fourfold composites of morphisms of abelian groups that agree agree on elements. -/
theorem apply_eq_of_comp₄_eq {X₀ X₁ X₂ X₃ X₄ Y₁ Y₂ Y₃ : AddCommGrpCat.{u}} {a : X₀ ⟶ X₁}
    {b : X₁ ⟶ X₂} {c : X₂ ⟶ X₃} {d : X₃ ⟶ X₄} {a' : X₀ ⟶ Y₁} {b' : Y₁ ⟶ Y₂} {c' : Y₂ ⟶ Y₃}
    {d' : Y₃ ⟶ X₄} (h : a ≫ b ≫ c ≫ d = a' ≫ b' ≫ c' ≫ d') (x : (X₀ : Type u)) :
    d (c (b (a x))) = d' (c' (b' (a' x))) := by
  simpa only [CategoryTheory.comp_apply] using ConcreteCategory.congr_hom h x

/-- Scalar multiplication on an obstruction module is the map of the obstruction functor along
scalar multiplication on the module of coefficients. -/
theorem obstructionFunctor_map_smul_id_apply {R : CommRingCat.{u}} {X : Scheme.{u}}
    (π : X ⟶ Spec R) (G : SheafOfModules.{u} X.ringCatSheaf) (M : ModuleCat.{u} R) (r : R)
    (o : ((obstructionFunctor π G).obj M : Type u)) :
    (obstructionFunctor π G).map (r • 𝟙 M) o = r • o := by
  rw [CategoryTheory.Functor.map_smul, CategoryTheory.Functor.map_id]
  rfl

/-- **The map of obstruction modules between two bases, computed on `W`.** For a ring map
`ψ : A → A'` under `Λ` and a map `φ : M → N` from an `A`-module to an `A'`-module which is
`A`-linear along `ψ`, the map `H¹(W_A, 𝓕_A ⊗_A M) → H¹(W_{A'}, 𝓕_{A'} ⊗_{A'} N)` which, read on
`W`, is `H¹(W, 𝓕 ⊗_Λ φ)`; it is `A`-linear along `ψ`. -/
def wObstructionMap (ψ : A ⟶ A') (hψ : Spec.preimage t ≫ ψ = Spec.preimage t')
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} A'}
    (φ : letI : Module A (N : Type u) := Module.compHom _ ψ.hom
      (M : Type u) →ₗ[A] (N : Type u)) :
    letI : Module A ((obstructionFunctor (topProj t' g) (topSheaf t' g F)).obj N : Type u) :=
      Module.compHom _ ψ.hom
    ((obstructionFunctor (topProj t g) (topSheaf t g F)).obj M : Type u) →ₗ[A]
      ((obstructionFunctor (topProj t' g) (topSheaf t' g F)).obj N : Type u) :=
  letI : Module A ((obstructionFunctor (topProj t' g) (topSheaf t' g F)).obj N : Type u) :=
    Module.compHom _ ψ.hom
  { toFun := fun o => wComparisonMap g F t t' 1 (restrictScalarsHomOfLinearMap ψ hψ φ) o
    map_add' := fun o₁ o₂ => map_add (wComparisonMap g F t t' 1
      (restrictScalarsHomOfLinearMap ψ hψ φ)).hom o₁ o₂
    map_smul' := fun a o => by
      let : Module A (N : Type u) := Module.compHom _ ψ.hom
      have key : (ModuleCat.restrictScalars (Spec.preimage t).hom).map (a • 𝟙 M) ≫
          restrictScalarsHomOfLinearMap ψ hψ φ =
        restrictScalarsHomOfLinearMap ψ hψ φ ≫
          (ModuleCat.restrictScalars (Spec.preimage t').hom).map (ψ a • 𝟙 N) := by
        ext m
        exact φ.map_smul a m
      have h₂ := congrArg (wComparisonMap g F t t' 1) key
      rw [wComparisonMap_comp, wComparisonMap_comp, wComparisonMap_restrictScalars_map,
        wComparisonMap_restrictScalars_map] at h₂
      have e₁ := (abCohomology_map_tensorSheafFunctor_map_apply _ _ (a • 𝟙 M) o).trans
        (obstructionFunctor_map_smul_id_apply _ _ M a o)
      have e₃ := fun y => (abCohomology_map_tensorSheafFunctor_map_apply (topProj t' g)
        (topSheaf t' g F) (ψ a • 𝟙 N) y).trans (obstructionFunctor_map_smul_id_apply _ _ N (ψ a) y)
      generalize wComparisonMap g F t t' 1 (restrictScalarsHomOfLinearMap ψ hψ φ) = W at h₂ ⊢
      generalize ((abCohomology (topProj t g)).functor 1).map
        ((tensorSheafFunctor (topProj t g) (topSheaf t g F)).map (a • 𝟙 M)) = X at h₂ e₁
      generalize ((abCohomology (topProj t' g)).functor 1).map
        ((tensorSheafFunctor (topProj t' g) (topSheaf t' g F)).map (ψ a • 𝟙 N)) = Y at h₂ e₃
      exact (congrArg W e₁).symm.trans ((apply_eq_of_comp_eq h₂ o).trans (e₃ (W o))) }

/-- `wObstructionMap` is `wComparisonMap` in degree one. -/
theorem wObstructionMap_apply (ψ : A ⟶ A') (hψ : Spec.preimage t ≫ ψ = Spec.preimage t')
    {M : ModuleCat.{u} A} {N : ModuleCat.{u} A'}
    (φ : letI : Module A (N : Type u) := Module.compHom _ ψ.hom
      (M : Type u) →ₗ[A] (N : Type u))
    (o : ((obstructionFunctor (topProj t g) (topSheaf t g F)).obj M : Type u)) :
    wObstructionMap g F t t' ψ hψ φ o =
      wComparisonMap g F t t' 1 (restrictScalarsHomOfLinearMap ψ hψ φ) o :=
  rfl

end ObstructionMap

/-! ### The sequence `0 → I → A' → A → 0` over `Λ`, functorially -/

section KernelHom

variable {B hS}

/-- The ring map of a morphism of site algebras over `Spec Λ` is a map under `Λ`. -/
theorem preimage_comp_ofHom_ringMap {a b : SiteAlgebra B (Spec (.of Λ)) hS}
    (f : SiteAlgebra.Hom a b) :
    Spec.preimage a.toScheme ≫ CommRingCat.ofHom f.ringMap = Spec.preimage b.toScheme :=
  preimage_comp_eq_of_over (t := a.toScheme) (t' := b.toScheme)
    ((Over.post B.inclusion).map f.specMap) _ f.specMap_spec

/-- **The morphism of sequences `0 → I → A' → A → 0` over `Λ` of a morphism of deformation
situations**: for a commutative square of ring maps `A → A₁` and `A' → A₁'` under `Λ` between
two deformation situations, the induced morphism of short exact sequences of `Λ`-modules. -/
def kernelShortComplexΛHom {a b : SiteAlgebra B (Spec (.of Λ)) hS}
    {s : DeformationSituation B (Spec (.of Λ)) hS a}
    {t : DeformationSituation B (Spec (.of Λ)) hS b}
    (f : SiteAlgebra.Hom a b) (f' : SiteAlgebra.Hom s.top t.top)
    (comm : t.hom.ringMap.comp f'.ringMap = f.ringMap.comp s.hom.ringMap) :
    kernelShortComplexΛ s ⟶ kernelShortComplexΛ t where
  τ₁ := (kernelShortComplexΛX₁Iso s).hom ≫
      restrictScalarsHomOfLinearMap (CommRingCat.ofHom f.ringMap) (preimage_comp_ofHom_ringMap f)
        (DeformationSituation.kernelMap s t f.ringMap f'.ringMap comm) ≫
      (kernelShortComplexΛX₁Iso t).inv
  τ₂ := restrictScalarsHomOfComp (CommRingCat.ofHom f'.ringMap) (preimage_comp_ofHom_ringMap f')
  τ₃ := (kernelShortComplexΛX₃Iso s).hom ≫
      restrictScalarsHomOfComp (CommRingCat.ofHom f.ringMap) (preimage_comp_ofHom_ringMap f) ≫
      (kernelShortComplexΛX₃Iso t).inv
  comm₁₂ := by
    ext z
    rfl
  comm₂₃ := by
    ext x
    exact RingHom.congr_fun comm x

/-- The first component of `kernelShortComplexΛHom`, read on the kernels. -/
@[reassoc]
theorem kernelShortComplexΛX₁Iso_hom_comp {a b : SiteAlgebra B (Spec (.of Λ)) hS}
    {s : DeformationSituation B (Spec (.of Λ)) hS a}
    {t : DeformationSituation B (Spec (.of Λ)) hS b}
    (f : SiteAlgebra.Hom a b) (f' : SiteAlgebra.Hom s.top t.top)
    (comm : t.hom.ringMap.comp f'.ringMap = f.ringMap.comp s.hom.ringMap) :
    (kernelShortComplexΛX₁Iso s).hom ≫
        restrictScalarsHomOfLinearMap (CommRingCat.ofHom f.ringMap)
          (preimage_comp_ofHom_ringMap f)
          (DeformationSituation.kernelMap s t f.ringMap f'.ringMap comm) =
      (kernelShortComplexΛHom f f' comm).τ₁ ≫ (kernelShortComplexΛX₁Iso t).hom := by
  simp [kernelShortComplexΛHom]

/-- The last component of `kernelShortComplexΛHom`, read on the bases: it is `A → A₁`. -/
@[reassoc]
theorem kernelShortComplexΛX₃Iso_inv_comp {a b : SiteAlgebra B (Spec (.of Λ)) hS}
    {s : DeformationSituation B (Spec (.of Λ)) hS a}
    {t : DeformationSituation B (Spec (.of Λ)) hS b}
    (f : SiteAlgebra.Hom a b) (f' : SiteAlgebra.Hom s.top t.top)
    (comm : t.hom.ringMap.comp f'.ringMap = f.ringMap.comp s.hom.ringMap) :
    (kernelShortComplexΛX₃Iso s).inv ≫ (kernelShortComplexΛHom f f' comm).τ₃ =
      restrictScalarsHomOfComp (CommRingCat.ofHom f.ringMap) (preimage_comp_ofHom_ringMap f) ≫
        (kernelShortComplexΛX₃Iso t).inv := by
  simp [kernelShortComplexΛHom]

end KernelHom

/-! ### The map of obstruction modules at a morphism of affine objects -/

section AffineObjectMap

variable {B hS}

/-- **The map of obstruction modules of clause (2) at a morphism of affine objects**: for a
morphism `(x, A) → (y, A₁)` and a map `φ : M → N` which is `A`-linear along `A → A₁`, the map
`H¹(W_A, 𝓕_A ⊗_A M) → H¹(W_{A₁}, 𝓕_{A₁} ⊗_{A₁} N)` of `wObstructionMap`, between the obstruction
modules of `affineObstruction`. -/
def affineWObstructionMap
    {P Q : AffineObject B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS)}
    (h : AffineObject.Hom P Q) {M : ModuleCat.{u} P.alg.carrier}
    {N : ModuleCat.{u} Q.alg.carrier}
    (φ : letI : Module P.alg.carrier (N : Type u) := Module.compHom _ h.alg.ringMap
      (M : Type u) →ₗ[P.alg.carrier] (N : Type u)) :
    letI : Module P.alg.carrier ((affineObstruction g F Q).functor.obj N : Type u) :=
      Module.compHom _ h.alg.ringMap
    ((affineObstruction g F P).functor.obj M : Type u) →ₗ[P.alg.carrier]
      ((affineObstruction g F Q).functor.obj N : Type u) :=
  wObstructionMap g F P.alg.toScheme Q.alg.toScheme (CommRingCat.ofHom h.alg.ringMap)
    (preimage_comp_ofHom_ringMap h.alg) φ

/-- `affineWObstructionMap` is `wComparisonMap` in degree one. -/
theorem affineWObstructionMap_apply
    {P Q : AffineObject B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS)}
    (h : AffineObject.Hom P Q) {M : ModuleCat.{u} P.alg.carrier}
    {N : ModuleCat.{u} Q.alg.carrier}
    (φ : letI : Module P.alg.carrier (N : Type u) := Module.compHom _ h.alg.ringMap
      (M : Type u) →ₗ[P.alg.carrier] (N : Type u))
    (o : ((affineObstruction g F P).functor.obj M : Type u)) :
    affineWObstructionMap g F h φ o =
      wComparisonMap g F P.alg.toScheme Q.alg.toScheme 1
        (restrictScalarsHomOfLinearMap (CommRingCat.ofHom h.alg.ringMap)
          (preimage_comp_ofHom_ringMap h.alg) φ) o :=
  rfl

/-- **`map_local`**: at an identity morphism of affine objects, `affineWObstructionMap` along a
map which is on elements an `A`-linear map `f` is the map `𝒪(f)` of the obstruction functor. -/
theorem affineWObstructionMap_id_apply
    (P : AffineObject B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS))
    {M N : ModuleCat.{u} P.alg.carrier} (f : M ⟶ N)
    (φ : letI : Module P.alg.carrier (N : Type u) :=
        Module.compHom _ (AffineObject.Hom.id P).alg.ringMap
      (M : Type u) →ₗ[P.alg.carrier] (N : Type u)) (hφ : ∀ m : (M : Type u), φ m = f m)
    (o : ((affineObstruction g F P).functor.obj M : Type u)) :
    affineWObstructionMap g F (AffineObject.Hom.id P) φ o =
      (affineObstruction g F P).functor.map f o := by
  have h₁ := affineWObstructionMap_apply g F (AffineObject.Hom.id P) φ o
  have h₂ := ConcreteCategory.congr_hom (wComparisonMap_eq_map g F P.alg.toScheme 1 f
      (restrictScalarsHomOfLinearMap (CommRingCat.ofHom (AffineObject.Hom.id P).alg.ringMap)
        (preimage_comp_ofHom_ringMap (AffineObject.Hom.id P).alg) φ) hφ) o
  have h₃ := abCohomology_map_tensorSheafFunctor_map_apply (topProj P.alg.toScheme g)
    (topSheaf P.alg.toScheme g F) f o
  have hf : (obstructionFunctor (topProj P.alg.toScheme g) (topSheaf P.alg.toScheme g F)).map f =
      (affineObstruction g F P).functor.map f := rfl
  have h₄ := ConcreteCategory.congr_hom hf o
  generalize wComparisonMap g F P.alg.toScheme P.alg.toScheme 1
    (restrictScalarsHomOfLinearMap (CommRingCat.ofHom (AffineObject.Hom.id P).alg.ringMap)
      (preimage_comp_ofHom_ringMap (AffineObject.Hom.id P).alg) φ) = X at h₁ h₂
  generalize ((abCohomology (topProj P.alg.toScheme g)).functor 1).map
    ((tensorSheafFunctor (topProj P.alg.toScheme g) (topSheaf P.alg.toScheme g F)).map f) = Y
    at h₂ h₃
  generalize (affineObstruction g F P).functor.map f = U at h₃ h₄ ⊢
  exact h₁.trans (h₂.trans (h₃.trans h₄))

/-- **`map_comp`**: `affineWObstructionMap` along a composite of morphisms of affine objects
and a composite of semilinear maps is the composite. -/
theorem affineWObstructionMap_comp_apply
    {P Q R : AffineObject B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS)}
    (h : AffineObject.Hom P Q) (k : AffineObject.Hom Q R) {M : ModuleCat.{u} P.alg.carrier}
    {N : ModuleCat.{u} Q.alg.carrier} {L : ModuleCat.{u} R.alg.carrier}
    (φ : letI : Module P.alg.carrier (N : Type u) := Module.compHom _ h.alg.ringMap
      (M : Type u) →ₗ[P.alg.carrier] (N : Type u))
    (ψ : letI : Module Q.alg.carrier (L : Type u) := Module.compHom _ k.alg.ringMap
      (N : Type u) →ₗ[Q.alg.carrier] (L : Type u))
    (χ : letI : Module P.alg.carrier (L : Type u) := Module.compHom _ (h.comp k).alg.ringMap
      (M : Type u) →ₗ[P.alg.carrier] (L : Type u)) (hχ : ∀ m : (M : Type u), χ m = ψ (φ m))
    (o : ((affineObstruction g F P).functor.obj M : Type u)) :
    affineWObstructionMap g F (h.comp k) χ o =
      affineWObstructionMap g F k ψ (affineWObstructionMap g F h φ o) := by
  have e : restrictScalarsHomOfLinearMap (CommRingCat.ofHom (h.comp k).alg.ringMap)
      (preimage_comp_ofHom_ringMap (h.comp k).alg) χ =
      restrictScalarsHomOfLinearMap (CommRingCat.ofHom h.alg.ringMap)
          (preimage_comp_ofHom_ringMap h.alg) φ ≫
        restrictScalarsHomOfLinearMap (CommRingCat.ofHom k.alg.ringMap)
          (preimage_comp_ofHom_ringMap k.alg) ψ := by
    ext m
    exact hχ m
  have h₁ := affineWObstructionMap_apply g F (h.comp k) χ o
  have h₂ := affineWObstructionMap_apply g F h φ o
  have h₃ := affineWObstructionMap_apply g F k ψ (affineWObstructionMap g F h φ o)
  have h₄ := (congrArg (wComparisonMap g F P.alg.toScheme R.alg.toScheme 1) e).trans
      (wComparisonMap_comp g F P.alg.toScheme Q.alg.toScheme R.alg.toScheme 1 _ _)
  generalize wComparisonMap g F P.alg.toScheme R.alg.toScheme 1
    (restrictScalarsHomOfLinearMap (CommRingCat.ofHom (h.comp k).alg.ringMap)
      (preimage_comp_ofHom_ringMap (h.comp k).alg) χ) = X at h₁ h₄
  generalize wComparisonMap g F P.alg.toScheme Q.alg.toScheme 1
    (restrictScalarsHomOfLinearMap (CommRingCat.ofHom h.alg.ringMap)
      (preimage_comp_ofHom_ringMap h.alg) φ) = Y at h₂ h₄
  generalize wComparisonMap g F Q.alg.toScheme R.alg.toScheme 1
    (restrictScalarsHomOfLinearMap (CommRingCat.ofHom k.alg.ringMap)
      (preimage_comp_ofHom_ringMap k.alg) ψ) = Z at h₃ h₄
  exact h₁.trans ((apply_eq_apply_of_eq_comp h₄ o).trans ((congrArg Z h₂).symm.trans h₃.symm))

end AffineObjectMap

/-! ### Conditions (ii) and (iii) -/

section Conditions

/-- Two functors applied to an equality of composites give an equality of composites. -/
private theorem map_map_comp_eq {C D E : Type*} [Category C] [Category D] [Category E]
    (G₁ : C ⥤ D) (G₂ : D ⥤ E) {X Y Z V : C} {a : X ⟶ Y} {b : Y ⟶ V} {c : X ⟶ Z} {d : Z ⟶ V}
    (h : a ≫ b = c ≫ d) :
    G₂.map (G₁.map a) ≫ G₂.map (G₁.map b) = G₂.map (G₁.map c) ≫ G₂.map (G₁.map d) := by
  simp only [← Functor.map_comp, h]

/-- **Condition (ii) of Stacks 07YG for the example of Stacks 07YH.** A morphism of deformation
situations `(x, A' → A) → (y, A₁' → A₁)` carries the obstruction element of `x` to that of `y`
under the map of obstruction modules along `A → A₁` and the map of kernels `I → I₁`. -/
theorem affineWObstructionMap_sectionsObstructionClass
    (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F)
    {P Q : AffineObject B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS)}
    {s : DeformationSituation B (Spec (.of Λ)) hS P.alg}
    {t : DeformationSituation B (Spec (.of Λ)) hS Q.alg}
    (m : DeformationSituation.Hom B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS) s t) :
    affineWObstructionMap g F m.base
        (DeformationSituation.kernelMap s t m.base.alg.ringMap m.top.ringMap m.comm)
        (sectionsObstructionClass B hS g F hF P s) =
      sectionsObstructionClass B hS g F hF Q t := by
  have : (tensorSheafFunctor g F).Additive := additive_tensorSheafFunctor g F
  refine (affineWObstructionMap_apply g F m.base _ _).trans
    ((wComparisonMap_apply_eq_iff g F _ _ 1 _ _ _).mpr ?_)
  rw [wComparison_sectionsObstructionClass, wComparison_sectionsObstructionClass,
    wComparison_naturality_section B hS g F m.base]
  have hδ : ((abCohomology g).functor 0).map ((tensorSheafFunctor g F).map
        (kernelShortComplexΛHom m.base.alg m.top m.comm).τ₃) ≫
        (abCohomology g).δ
          (tensorSheafFunctor_shortExact g F hF (kernelShortComplexΛ_shortExact t)) 0 =
      (abCohomology g).δ
          (tensorSheafFunctor_shortExact g F hF (kernelShortComplexΛ_shortExact s)) 0 ≫
        ((abCohomology g).functor 1).map
          (X := (tensorSheafFunctor g F).obj (kernelShortComplexΛ s).X₁)
          ((tensorSheafFunctor g F).map
            (kernelShortComplexΛHom m.base.alg m.top m.comm).τ₁) :=
    (abCohomology g).δ_naturality
      (tensorSheafFunctor_shortExact g F hF (kernelShortComplexΛ_shortExact s))
      (tensorSheafFunctor_shortExact g F hF (kernelShortComplexΛ_shortExact t))
      ((tensorSheafFunctor g F).mapShortComplex.map
        (kernelShortComplexΛHom m.base.alg m.top m.comm)) 0
  have hmor : ((abCohomology g).functor 0).map
        ((tensorSheafFunctor g F).map (kernelShortComplexΛX₃Iso s).inv) ≫
      (abCohomology g).δ
          (tensorSheafFunctor_shortExact g F hF (kernelShortComplexΛ_shortExact s)) 0 ≫
        ((abCohomology g).functor 1).map
          (X := (tensorSheafFunctor g F).obj (kernelShortComplexΛ s).X₁)
          ((tensorSheafFunctor g F).map (kernelShortComplexΛX₁Iso s).hom) ≫
        ((abCohomology g).functor 1).map ((tensorSheafFunctor g F).map
          (restrictScalarsHomOfLinearMap (CommRingCat.ofHom m.base.alg.ringMap)
            (preimage_comp_ofHom_ringMap m.base.alg)
            (DeformationSituation.kernelMap s t m.base.alg.ringMap m.top.ringMap m.comm))) =
      ((abCohomology g).functor 0).map ((tensorSheafFunctor g F).map
          (restrictScalarsHomOfComp (CommRingCat.ofHom m.base.alg.ringMap)
            (preimage_comp_ofHom_ringMap m.base.alg))) ≫
        ((abCohomology g).functor 0).map
          ((tensorSheafFunctor g F).map (kernelShortComplexΛX₃Iso t).inv) ≫
        (abCohomology g).δ
          (tensorSheafFunctor_shortExact g F hF (kernelShortComplexΛ_shortExact t)) 0 ≫
        ((abCohomology g).functor 1).map
          (X := (tensorSheafFunctor g F).obj (kernelShortComplexΛ t).X₁)
          ((tensorSheafFunctor g F).map (kernelShortComplexΛX₁Iso t).hom) := by
    have h₁ := map_map_comp_eq (tensorSheafFunctor g F) ((abCohomology g).functor 1)
      (kernelShortComplexΛX₁Iso_hom_comp m.base.alg m.top m.comm)
    have h₃ := map_map_comp_eq (tensorSheafFunctor g F) ((abCohomology g).functor 0)
      (kernelShortComplexΛX₃Iso_inv_comp m.base.alg m.top m.comm).symm
    rw [h₁, reassoc_of% hδ.symm, reassoc_of% h₃]
  exact apply_eq_of_comp₄_eq hmor _

/-- Transport of the statement "`y` has a preimage under `G.map m`" along equalities of the
objects and of the data. -/
theorem exists_map_apply_eq_iff_of_heq {C : Type*} [Category C] (G : C ⥤ AddCommGrpCat.{u})
    {X₁ X₂ Y₁ Y₂ : C} (hX : X₁ = X₂) (hY : Y₁ = Y₂) (m₁ : X₁ ⟶ Y₁) (m₂ : X₂ ⟶ Y₂)
    (hm : HEq m₁ m₂) (y₁ : ToType (G.obj Y₁)) (y₂ : ToType (G.obj Y₂)) (hy : HEq y₁ y₂) :
    (∃ x : ToType (G.obj X₁), G.map m₁ x = y₁) ↔ ∃ x : ToType (G.obj X₂), G.map m₂ x = y₂ := by
  subst hX hY
  cases hm
  cases hy
  rfl

/-- The restriction maps of `sectionsPresheaf` are those of `sectionsPresheafOver`, in the form
of the statement that an element is a restriction. -/
theorem exists_sectionsPresheaf_map_eq_iff {S W : Scheme.{u}} (q : W ⟶ S) (𝓕 : W.Modules)
    [𝓕.IsQuasicoherent] (B : BigFppfSite.{u}) (hS : B.Contains S)
    {U V : BigFppfOver B S hS} (f : V ⟶ U) (x : (sectionsPresheaf q 𝓕 B hS).obj (op V)) :
    (∃ s : (sectionsPresheaf q 𝓕 B hS).obj (op U), (sectionsPresheaf q 𝓕 B hS).map f.op s = x) ↔
      ∃ s : ToType ((sectionsPresheafOver q 𝓕).obj ((siteToOver B hS).op.obj (op U))),
        (sectionsPresheafOver q 𝓕).map ((siteToOver B hS).op.map f.op) s = x :=
  Iff.rfl

/-- **The lifting criterion of the category of elements, through the boundary of a section.**
An object `x` over `Spec A` of the category of elements of `sectionsPresheaf` lifts across a
deformation situation `A' → A` exactly when the boundary of the section of `𝓕_A` it names,
computed on `W_{A'}`, vanishes. -/
theorem hasLift_iff_thickeningClass_eq_zero
    (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F)
    (P : AffineObject B (Spec (.of Λ)) hS
      (PresheafOfCategories.discreteProjection (sectionsPresheaf g F B hS)))
    (t : DeformationSituation B (Spec (.of Λ)) hS P.alg) :
    AffineObject.HasLift (Functor.IsFiberedInSets.isFiberedInGroupoids _) P t ↔
      thickeningClass g F hF t
        (PresheafOfCategories.discreteFiberEquiv (sectionsPresheaf g F B hS) P.alg.over
          P.obj) = 0 :=
  ((hasLift_iff_exists_section_sectionsPresheaf g F B hS P t).trans
    (exists_sectionsPresheaf_map_eq_iff g F B hS t.hom.specMap _)).trans
    ((exists_map_apply_eq_iff_of_heq (sectionsPresheafOver g F)
      (X₁ := (siteToOver B hS).op.obj (op t.top.over)) (X₂ := op (Over.mk t.top.toScheme))
      (Y₁ := (siteToOver B hS).op.obj (op P.alg.over)) (Y₂ := op (Over.mk P.alg.toScheme))
      rfl rfl ((siteToOver B hS).op.map t.hom.specMap.op) (thickeningOver t).op HEq.rfl
      (PresheafOfCategories.discreteFiberEquiv (sectionsPresheaf g F B hS) P.alg.over P.obj)
      (PresheafOfCategories.discreteFiberEquiv (sectionsPresheaf g F B hS) P.alg.over P.obj)
      HEq.rfl).trans
      (thickeningClass_eq_zero_iff g F hF t
        (PresheafOfCategories.discreteFiberEquiv (sectionsPresheaf g F B hS) P.alg.over
          P.obj)).symm)

/-- The obstruction element vanishes exactly when the boundary of the section, computed on
`W_{A'}`, does: the two are identified by the isomorphism `thickeningIso`. -/
theorem sectionsObstructionClass_eq_zero_iff
    (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F)
    (P : AffineObject B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS))
    (t : DeformationSituation B (Spec (.of Λ)) hS P.alg) :
    sectionsObstructionClass B hS g F hF P t = 0 ↔
      thickeningClass g F hF t (affineObjectSection B hS g F P) = 0 := by
  have key : ∀ {X Y : AddCommGrpCat.{u}} (e : X ≅ Y) (x : (X : Type u)), e.hom x = 0 ↔ x = 0 :=
    fun e x => ⟨fun h => by simpa using congrArg e.inv h, fun h => by rw [h, map_zero]⟩
  exact key ((DeltaFunctor.isoApp (thickeningIso (topProj t.top.toScheme g)
    (baseChangeMap g (thickeningOver t)) (topProj P.alg.toScheme g)) 1).app _) _

/-- **Condition (iii) of Stacks 07YG for the example of Stacks 07YH.** An object `x` over
`Spec A` lifts across a deformation situation `A' → A` exactly when its obstruction element
vanishes. -/
theorem hasLift_iff_sectionsObstructionClass_eq_zero
    (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F)
    (P : AffineObject B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS))
    (t : DeformationSituation B (Spec (.of Λ)) hS P.alg) :
    AffineObject.HasLift (Functor.IsFiberedInSets.isFiberedInGroupoids _) P t ↔
      sectionsObstructionClass B hS g F hF P t = 0 :=
  (hasLift_iff_thickeningClass_eq_zero B hS g F hF P t).trans
    (sectionsObstructionClass_eq_zero_iff B hS g F hF P t).symm

end Conditions

/-! ### The obstruction theory -/

section Theory

/-- **The obstruction theory of Stacks 07YH**, for the category fibred in groupoids `𝒳` of the
functor `T/S ↦ H⁰(W_T, 𝓕_T)` over `S = Spec Λ`, `𝓕` quasi-coherent and flat over `S`. The
obstruction modules at an object over `Spec A` are `H¹(W_A, 𝓕_A ⊗_A M)` (`affineObstruction`);
the map of obstruction modules along a morphism `(x, A) → (y, A₁)` and an `A`-linear map
`M → N` is `H¹(W, 𝓕 ⊗_Λ (M → N))` read through the comparisons with `W` (`wObstructionMap`); the
obstruction element of a deformation situation is the boundary of the section named by `x`
(`sectionsObstructionClass`). -/
def sectionsObstructionTheory (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F) :
    ObstructionTheory B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS)
      (Functor.IsFiberedInSets.isFiberedInGroupoids _) where
  obstruction := affineObstruction g F
  map P Q h M N φ := affineWObstructionMap g F h φ
  map_local P M N f :=
    let φ : (letI : Module P.alg.carrier (N : Type u) :=
        Module.compHom _ (AffineObject.Hom.id P).alg.ringMap
      (M : Type u) →ₗ[P.alg.carrier] (N : Type u)) :=
      { toFun := f
        map_add' := map_add f.hom
        map_smul' := fun a m => f.hom.map_smul a m }
    ⟨φ, fun _ => rfl, fun o => affineWObstructionMap_id_apply g F P f φ (fun _ => rfl) o⟩
  map_id P M :=
    let φ : (letI : Module P.alg.carrier (M : Type u) :=
        Module.compHom _ (AffineObject.Hom.id P).alg.ringMap
      (M : Type u) →ₗ[P.alg.carrier] (M : Type u)) :=
      { toFun := fun m => m
        map_add' := fun _ _ => rfl
        map_smul' := fun _ _ => rfl }
    ⟨φ, fun _ => rfl, fun o => (affineWObstructionMap_id_apply g F P (𝟙 M) φ
      (fun m => (CategoryTheory.id_apply m).symm) o).trans (by
        rw [CategoryTheory.Functor.map_id]
        exact CategoryTheory.id_apply o)⟩
  map_comp P Q R h k M N L φ ψ := by
    let : Module P.alg.carrier (N : Type u) := Module.compHom _ h.alg.ringMap
    let : Module Q.alg.carrier (L : Type u) := Module.compHom _ k.alg.ringMap
    let : Module P.alg.carrier (L : Type u) := Module.compHom _ (h.comp k).alg.ringMap
    let χ : (M : Type u) →ₗ[P.alg.carrier] (L : Type u) :=
      { toFun := fun m => ψ (φ m)
        map_add' := fun m₁ m₂ => by rw [φ.map_add, ψ.map_add]
        map_smul' := fun a m => (congrArg ψ (φ.map_smul a m)).trans
          (ψ.map_smul (h.alg.ringMap a) (φ m)) }
    exact ⟨χ, fun _ => rfl, fun o => affineWObstructionMap_comp_apply g F h k φ ψ χ
      (fun _ => rfl) o⟩
  obs := sectionsObstructionClass B hS g F hF
  obs_naturality P Q s t m :=
    ⟨DeformationSituation.kernelMap s t m.base.alg.ringMap m.top.ringMap m.comm, fun _ => rfl,
      affineWObstructionMap_sectionsObstructionClass B hS g F hF m⟩
  hasLift_iff_obs_eq_zero := hasLift_iff_sectionsObstructionClass_eq_zero B hS g F hF

/-- **Stacks 07YH.** Let `S = Spec Λ` with `Λ` Noetherian, `W → S` a morphism of schemes and `𝓕` a
quasi-coherent `𝒪_W`-module flat over `S`. The category fibred in groupoids `𝒳` attached to
`F : T/S ↦ H⁰(W_T, 𝓕_T)` has an obstruction theory (Stacks 07YG) whose obstruction modules at an
object `x` over `Spec A` are `𝒪_x(M) = H¹(W_A, 𝓕_A ⊗_A M)` (`affineObstruction`, i.e.
`obstructionFunctor`, as a functor of `M`), and whose obstruction element at a deformation
situation `(x, A' → A)` is the image of `x` under the boundary map
`H⁰(W_A, 𝓕_A) → H¹(W_A, 𝓕_A ⊗_A I)` of `0 → 𝓕_A ⊗_A I → 𝓕_{A'} → 𝓕_A → 0`. -/
@[stacks 07YH]
theorem exists_obstructionTheory [IsNoetherianRing Λ]
    (hF : AlgebraicGeometry.IsFlatOver g.toLRSHom.toShHom F) :
    ∃ θ : ObstructionTheory B (Spec (.of Λ)) hS (sectionsFibredCategory g F B hS)
        (Functor.IsFiberedInSets.isFiberedInGroupoids _),
      ∃ e : ∀ P, (θ.obstruction P).functor ≅ (affineObstruction g F P).functor,
        ∀ P t, (e P).hom.app t.kernelObj (θ.obs P t) = sectionsObstructionClass B hS g F hF P t :=
  ⟨sectionsObstructionTheory B hS g F hF, fun P => Iso.refl (affineObstruction g F P).functor,
    fun _ _ => rfl⟩

end Theory

end Deformation.Artin.SectionsSheaf

end
