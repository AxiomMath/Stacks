module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.OnSpaceMonoidal
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.PullbackUnitGenerators
public import StacksFrontier.AlgebraicGeometry.DeRham.StructureSheafConnection
public import StacksFrontier.AlgebraicGeometry.DeRham.WedgeComponentRestrictScalars

/-!
# The wedge comparison is an epimorphism when the image of `c` generates

Let `φ : A ⟶ 𝒪_X` be a morphism of sheaves of commutative rings on a space, let `M`, `N` be
sheaves of `𝒪_X`-modules and let `c : Q ⟶ M|_A` be a morphism of sheaves of `A`-modules into the
restriction of scalars of `M`. The two tensor products are compared by the lax morphism

`(M|_A) ⊗_A (N|_A) ⟶ (M ⊗_{𝒪_X} N)|_A`

of `StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorRestrictScalarsLax`, which is an
epimorphism (`Stacks.SheafOfModules.TensorRestrictScalars.epi_laxComparison`). **This file proves
that its composite with `c ⊗ 1`,**

`Q ⊗_A (N|_A) ⟶ (M ⊗_{𝒪_X} N)|_A`,

**is an epimorphism as soon as the image of `c` generates `M` locally over `𝒪_X`.** The reason is
the one-line computation that a local pure tensor `x ⊗ η` with `x = Σ aᵢ·c(qᵢ)` is
`Σ c(qᵢ) ⊗ (aᵢ·η)`: the `𝒪_X`-linearity of the right-hand factor moves the scalars across, and
pure tensors over `A` need not be in the image while pure tensors over `𝒪_X` are.

This is the shape in which [Stacks, Section 0FMK] needs the surjective half of the underived
identity `F ⊗_{𝒪_X} f^*G ≅ F ⊗_{f^{-1}𝒪_Y} f^{-1}G` of [Stacks, Tag 08DE]: there `Q` is
`f^{-1}Ω^k_{Y/S}`, `M` is `⋀^k(f^*Ω_{Y/S})`, `A` is `(f∘g)^{-1}𝒪_S`, and the local generation of
`M` by the image of `c` is local generation of a pullback by the pullback-unit sections
(`Stacks.PullbackUnitGenerators.mem_localUnitSpan`) carried along the comparison of
[Stacks, Tag 01CI]; the epimorphy hypothesis of
`AlgebraicGeometry.SheafOfModules.imageSubobject_summand_eq_exteriorImageFiltration` is exactly
the conclusion below.

## Main definitions

* `AlgebraicGeometry.SheafOfModules.comparisonSections`: the local sections of `M` in the image
  of `c`, a family of subsets of the sections of `M` stable under restriction.

## Main results

* `AlgebraicGeometry.SheafOfModules.epi_tensorFunctor_map_comp_laxComparison`: **`c ⊗ 1`
  followed by the lax comparison is an epimorphism** when every local section of `M` lies in the
  local `𝒪_X`-span of the image of `c`.
* `AlgebraicGeometry.SheafOfModules.apply_toTensorSheafSection_eq_zero`: the computation behind
  it — a morphism out of `(M ⊗_{𝒪_X} N)|_A` killing every `c(q) ⊗ η` kills every `x ⊗ η`.
* `AlgebraicGeometry.SheafOfModules.mem_localSpan_map` and
  `AlgebraicGeometry.SheafOfModules.mem_spanSubmodule_map`: a morphism of sheaves of modules
  carries the (local) span of a family of local sections into the (local) span of the image
  family. `AlgebraicGeometry.SheafOfModules.mem_localSpan_comparisonSections_of_iso` is the
  consequence used downstream: local generation by the image of `c` is inherited by
  `c` followed by the restriction of scalars of an isomorphism.

## Implementation notes

**The proof is by cancellation, not by local surjectivity.** A morphism `g` out of
`(M ⊗_{𝒪_X} N)|_A` killing the composite is shown to vanish: the lax comparison is an
epimorphism, so it is enough that `g` kill every local pure tensor over `A`
(`Stacks.SheafOfModules.OnSpace.tensor_hom_ext`), i.e. every `x ⊗ η` over `𝒪_X`. Local generation
is a statement about a covering sieve, so the vanishing is first proved for `x` in the honest
span (`Submodule.span_induction` — the scalar case is where the local section of `𝒪_X` crosses
the tensor, by `AlgebraicGeometry.Scheme.Hom.toTensorSheafSection_smul_tmul` and
`toTensorSheafSection_tmul_smul`) and then globalised by separatedness of `Z`
(`Stacks.eq_of_isSeparated`). Doing it the other way round — proving the composite locally
surjective — would need an intersection of covering sieves for each of the finitely many pure
tensors a local section of the target decomposes into, which the sieve calculus here does not
provide.

**The sheaves of `𝒪_X`-modules are taken at the `RingedSpaceModuleAdjunction.structureSheafRing`
spelling** rather than at `Sheaf.toRingCat _ X.sheaf`, which is the spelling
`StacksFrontier.AlgebraicGeometry.DeRham.WedgeComponentRestrictScalars` uses. The two are the same
sheaf of rings, but only the former is `@[instance_reducible]`, so only at the former does
instance search find the action of `X.presheaf.obj U` on the sections of `M` — which is the
action the tensor product of
`StacksFrontier.Algebra.Category.ModuleCat.Sheaf.TensorStalkRingedSpace` and all of its section
formulas are written over. At the other spelling every pure tensor has to be written with its
module instances supplied by unification against an expected type, and none of
`TensorProduct.add_tmul`, `zero_tmul` or `smul_tmul'` can be named.

## References

* [Stacks Project, Tag 01CA](https://stacks.math.columbia.edu/tag/01CA)
* [Stacks Project, Tag 03CU](https://stacks.math.columbia.edu/tag/03CU)
* [Stacks Project, Tag 08DE](https://stacks.math.columbia.edu/tag/08DE)
* [Stacks Project, Tag 0FMK](https://stacks.math.columbia.edu/tag/0FMK)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open RingedSpaceModuleAdjunction
open scoped TensorProduct
open Stacks.SheafOfModules.TensorRestrictScalars (laxComparison epi_laxComparison
  restrictScalarsSheaf)
open Stacks.SheafOfModules.TensorStalkRingedSpace (toTensorSheafSection)

universe u

namespace AlgebraicGeometry.SheafOfModules

variable {X : RingedSpace.{u, u}} {A : TopCat.Sheaf CommRingCat.{u} X.carrier} {φ : A ⟶ X.sheaf}
  {Q : _root_.SheafOfModules.{u} (underlyingRingSheaf A)}
  {M N : _root_.SheafOfModules.{u} (structureSheafRing X)}

attribute [local instance] _root_.SheafOfModules.instAbelian

/-- **The local sections of `M` in the image of `c`**, as a family of subsets of the sections of
`M` indexed by the opens of `X`. Naturality of `c` makes the family stable under restriction
(`AlgebraicGeometry.SheafOfModules.map_mem_comparisonSections`), which is what lets the span of
the family be taken over each open separately. -/
def comparisonSections
    (c : Q ⟶ (_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj M)
    (U : (Opens X.carrier)ᵒᵖ) : Set (M.val.obj U) :=
  {x | ∃ q : Q.val.obj U, c.val.app U q = x}

/-- A restriction of a local section in the image of `c` is again in the image of `c`: this is
naturality of `c`. -/
theorem map_mem_comparisonSections
    (c : Q ⟶ (_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj M)
    {U V : (Opens X.carrier)ᵒᵖ} (k : U ⟶ V) {x : M.val.obj U} (hx : x ∈ comparisonSections c U) :
    M.val.map k x ∈ comparisonSections c V := by
  obtain ⟨q, rfl⟩ := hx
  exact ⟨Q.val.map k q, PresheafOfModules.naturality_apply c.val k q⟩

variable {M' : _root_.SheafOfModules.{u} (structureSheafRing X)}

/-- **A morphism of sheaves of `𝒪_X`-modules carries the span of a family of local sections into
the span of the image family.** Each generator goes to a restriction of an image of a member, by
naturality, and the span is spanned over the same ring on both sides, `ψ` being `𝒪_X`-linear. -/
theorem mem_spanSubmodule_map (ψ : M ⟶ M')
    {T : ∀ U : (Opens X.carrier)ᵒᵖ, Set (M.val.obj U)}
    {T' : ∀ U : (Opens X.carrier)ᵒᵖ, Set (M'.val.obj U)}
    (hT : ∀ (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj U), x ∈ T U → ψ.val.app U x ∈ T' U)
    {U : (Opens X.carrier)ᵒᵖ} {x : M.val.obj U}
    (hx : x ∈ (Stacks.SheafOfModules.spanSubmodule M T).obj U) :
    ψ.val.app U x ∈ (Stacks.SheafOfModules.spanSubmodule M' T').obj U := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨W, k, w, hw, rfl⟩ := hz
      rw [PresheafOfModules.naturality_apply ψ.val k w]
      exact Stacks.SheafOfModules.map_mem_spanSubmodule (T := T') k (hT W w hw)
  | zero =>
      rw [map_zero]
      exact Submodule.zero_mem _
  | add z w _ _ ihz ihw =>
      rw [map_add]
      exact Submodule.add_mem _ ihz ihw
  | smul a z _ ih =>
      rw [map_smul]
      exact Submodule.smul_mem _ a ih

/-- **A morphism of sheaves of `𝒪_X`-modules carries the local span of a family of local sections
into the local span of the image family**: the span sieve of a section is contained in the span
sieve of its image, by
`AlgebraicGeometry.SheafOfModules.mem_spanSubmodule_map` applied along each of its arrows. -/
theorem mem_localSpan_map (ψ : M ⟶ M')
    {T : ∀ U : (Opens X.carrier)ᵒᵖ, Set (M.val.obj U)}
    {T' : ∀ U : (Opens X.carrier)ᵒᵖ, Set (M'.val.obj U)}
    (hT : ∀ (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj U), x ∈ T U → ψ.val.app U x ∈ T' U)
    {U : (Opens X.carrier)ᵒᵖ} {x : M.val.obj U}
    (hx : x ∈ (Stacks.SheafOfModules.localSpan M T).obj U) :
    ψ.val.app U x ∈ (Stacks.SheafOfModules.localSpan M' T').obj U := by
  refine (Stacks.SheafOfModules.mem_localSpan_iff _).2
    (GrothendieckTopology.superset_covering _ ?_
      ((Stacks.SheafOfModules.mem_localSpan_iff x).1 hx))
  intro W i hi
  refine Eq.mpr (congrArg (· ∈ (Stacks.SheafOfModules.spanSubmodule M' T').obj (op W))
    (PresheafOfModules.naturality_apply ψ.val i.op x).symm) ?_
  exact mem_spanSubmodule_map ψ hT ((Stacks.SheafOfModules.spanSieve_arrows x i).1 hi)

/-- The image under `ψ` of a local section in the image of `c` is in the image of `c` followed by
the restriction of scalars of `ψ`. -/
theorem map_mem_comparisonSections_comp
    (c : Q ⟶ (_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj M)
    (ψ : M ⟶ M') (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj U)
    (hx : x ∈ comparisonSections c U) :
    ψ.val.app U x ∈ comparisonSections
      (c ≫ (_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).map ψ) U := by
  obtain ⟨q, rfl⟩ := hx
  exact ⟨q, rfl⟩

/-- **Local generation by the image of `c` is inherited by `c` followed by the restriction of
scalars of an isomorphism.** This is how the hypothesis of
`AlgebraicGeometry.SheafOfModules.epi_tensorFunctor_map_comp_laxComparison` is obtained for a
comparison which lands in an exterior power only after the comparison of [Stacks, Tag 01CI]: the
generation statement available is the one for the pullback itself. -/
theorem mem_localSpan_comparisonSections_of_iso
    (c : Q ⟶ (_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj M)
    (e : M ≅ M')
    (hgen : ∀ (V : (Opens X.carrier)ᵒᵖ) (x : M.val.obj V),
      x ∈ (Stacks.SheafOfModules.localSpan M (comparisonSections c)).obj V)
    (U : (Opens X.carrier)ᵒᵖ) (x : M'.val.obj U) :
    x ∈ (Stacks.SheafOfModules.localSpan M'
      (comparisonSections (c ≫ (_root_.SheafOfModules.restrictScalars
        (underlyingRingHom (φ := φ))).map e.hom))).obj U := by
  refine Eq.mp (congrArg (· ∈ (Stacks.SheafOfModules.localSpan M'
      (comparisonSections (c ≫ (_root_.SheafOfModules.restrictScalars
        (underlyingRingHom (φ := φ))).map e.hom))).obj U)
    (congrArg (fun ψ : M' ⟶ M' => (ψ.val.app U) x) e.inv_hom_id)) ?_
  exact mem_localSpan_map e.hom (map_mem_comparisonSections_comp c e.hom)
    (hgen U (e.inv.val.app U x))

/-- **A morphism out of `(M ⊗_{𝒪_X} N)|_A` killing every `c(q) ⊗ η` kills `x ⊗ η` for every `x`
in the span of the image of `c`.** The scalar step is the whole point: `(a·x) ⊗ η = x ⊗ (a·η)`,
so a scalar multiple of a generator is handled by the inductive hypothesis at the rescaled second
factor, and that is why the second factor has to be quantified inside the induction. -/
theorem apply_toTensorSheafSection_eq_zero_of_mem_spanSubmodule
    (c : Q ⟶ (_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj M)
    {Z : _root_.SheafOfModules.{u} (underlyingRingSheaf A)}
    (g : (restrictScalarsSheaf A X.sheaf φ).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).obj N) ⟶ Z)
    (hg : ∀ (V : (Opens X.carrier)ᵒᵖ) (q : Q.val.obj V) (y : N.val.obj V),
      g.val.app V (toTensorSheafSection X M N V
        (c.val.app V q ⊗ₜ[X.presheaf.obj V] y)) = 0)
    {U : (Opens X.carrier)ᵒᵖ} {x : M.val.obj U}
    (hx : x ∈ (Stacks.SheafOfModules.spanSubmodule M (comparisonSections c)).obj U) :
    ∀ y : N.val.obj U,
      g.val.app U (toTensorSheafSection X M N U (x ⊗ₜ[X.presheaf.obj U] y)) = 0 := by
  induction hx using Submodule.span_induction with
  | mem z hz =>
      obtain ⟨W, k, w, hw, rfl⟩ := hz
      obtain ⟨q, hq⟩ := map_mem_comparisonSections c k hw
      intro y
      exact (congrArg (fun t : M.val.obj U => g.val.app U
        (toTensorSheafSection X M N U (t ⊗ₜ[X.presheaf.obj U] y))) hq).symm.trans (hg U q y)
  | zero =>
      intro y
      refine Eq.trans (congrArg (g.val.app U) ?_) (map_zero (g.val.app U).hom)
      exact Eq.trans (congrArg (toTensorSheafSection X M N U) (TensorProduct.zero_tmul _ y))
        (map_zero ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
          (PresheafOfModules.tensorObj (O := X.presheaf) M.val N.val)).app U).hom)
  | add z w _ _ ihz ihw =>
      intro y
      have h1 : toTensorSheafSection X M N U ((z + w) ⊗ₜ[X.presheaf.obj U] y) =
          toTensorSheafSection X M N U (z ⊗ₜ[X.presheaf.obj U] y) +
            toTensorSheafSection X M N U (w ⊗ₜ[X.presheaf.obj U] y) :=
        Eq.trans (congrArg (toTensorSheafSection X M N U) (TensorProduct.add_tmul z w y))
          (map_add ((Stacks.SheafOfModules.TensorStalkRingedSpace.sheafifyUnit X
            (PresheafOfModules.tensorObj (O := X.presheaf) M.val N.val)).app U).hom
            _ _)
      refine Eq.trans (congrArg (g.val.app U) h1) ?_
      exact Eq.trans (map_add (g.val.app U).hom _ _)
        (Eq.trans (congrArg₂ (· + ·) (ihz y) (ihw y)) (add_zero 0))
  | smul a z _ ih =>
      intro y
      refine Eq.trans (congrArg (fun t => g.val.app U t) ?_) (ih (a • y))
      exact Eq.trans (AlgebraicGeometry.Scheme.Hom.toTensorSheafSection_smul_tmul X M N U a z y)
        (AlgebraicGeometry.Scheme.Hom.toTensorSheafSection_tmul_smul X M N U a z y).symm

/-- **A morphism out of `(M ⊗_{𝒪_X} N)|_A` killing every `c(q) ⊗ η` kills every local pure
tensor**, when the image of `c` generates `M` locally. Local generation gives a covering sieve
along whose arrows the first factor lies in the honest span, where
`AlgebraicGeometry.SheafOfModules.apply_toTensorSheafSection_eq_zero_of_mem_spanSubmodule`
applies; restriction of a local pure tensor restricts its factors, and the target is a sheaf,
hence separated. -/
theorem apply_toTensorSheafSection_eq_zero
    (c : Q ⟶ (_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj M)
    (hgen : ∀ (V : (Opens X.carrier)ᵒᵖ) (x : M.val.obj V),
      x ∈ (Stacks.SheafOfModules.localSpan M (comparisonSections c)).obj V)
    {Z : _root_.SheafOfModules.{u} (underlyingRingSheaf A)}
    (g : (restrictScalarsSheaf A X.sheaf φ).obj
      (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} X.sheaf).obj M).obj N) ⟶ Z)
    (hg : ∀ (V : (Opens X.carrier)ᵒᵖ) (q : Q.val.obj V) (y : N.val.obj V),
      g.val.app V (toTensorSheafSection X M N V
        (c.val.app V q ⊗ₜ[X.presheaf.obj V] y)) = 0)
    (U : (Opens X.carrier)ᵒᵖ) (x : M.val.obj U) (y : N.val.obj U) :
    g.val.app U (toTensorSheafSection X M N U (x ⊗ₜ[X.presheaf.obj U] y)) = 0 := by
  refine Stacks.eq_of_isSeparated Z
    ((Stacks.SheafOfModules.mem_localSpan_iff x).1 (hgen U x)) ?_
  intro V i hi
  refine Eq.trans ?_ (map_zero (Z.val.map i.op).hom).symm
  refine Eq.trans (PresheafOfModules.naturality_apply g.val i.op
    (toTensorSheafSection X M N U (x ⊗ₜ[X.presheaf.obj U] y))).symm ?_
  refine Eq.trans (congrArg (g.val.app (op V))
    (Stacks.SheafOfModules.OnSpace.tensorSection_restrict X M N i x y)) ?_
  exact apply_toTensorSheafSection_eq_zero_of_mem_spanSubmodule c g hg
    ((Stacks.SheafOfModules.spanSieve_arrows x i).1 hi) _

/-- **`c ⊗ 1` followed by the lax comparison of the two tensor products is an epimorphism**, as
soon as every local section of `M` lies in the local `𝒪_X`-span of the image of `c`:

`Q ⊗_A (N|_A) ⟶ (M|_A) ⊗_A (N|_A) ⟶ (M ⊗_{𝒪_X} N)|_A`.

This is the epimorphy hypothesis of
`AlgebraicGeometry.SheafOfModules.imageSubobject_summand_eq_exteriorImageFiltration`, and the
form in which [Stacks, Section 0FMK] uses the surjective half of the underived identity of
[Stacks, Tag 08DE]. No hypothesis is placed on `φ`, on `N` or on `Q`. -/
theorem epi_tensorFunctor_map_comp_laxComparison
    (c : Q ⟶ (_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj M)
    (N : _root_.SheafOfModules.{u} (structureSheafRing X))
    (hgen : ∀ (V : (Opens X.carrier)ᵒᵖ) (x : M.val.obj V),
      x ∈ (Stacks.SheafOfModules.localSpan M (comparisonSections c)).obj V) :
    Epi (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).map c).app
        ((_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj N) ≫
      laxComparison A X.sheaf φ M N) := by
  refine (Preadditive.epi_iff_cancel_zero _).2 ?_
  intro Z g hg
  have := epi_laxComparison A X.sheaf φ M N
  have hg0 : ∀ (V : (Opens X.carrier)ᵒᵖ) (q : Q.val.obj V) (y : N.val.obj V),
      g.val.app V (toTensorSheafSection X M N V
        (c.val.app V q ⊗ₜ[X.presheaf.obj V] y)) = 0 := by
    intro V q y
    have e : (((Stacks.SheafOfModules.Tensor.sheafTensor.{u, u, u, u, u} A).map c).app
          ((_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj N) ≫
        laxComparison A X.sheaf φ M N).val.app V
          ((PresheafOfModules.tensorSheafUnit Q
            ((_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj N)).app V
            (q ⊗ₜ[A.obj.obj V] y)) =
        toTensorSheafSection X M N V (c.val.app V q ⊗ₜ[X.presheaf.obj V] y) :=
      Eq.trans (congrArg ((laxComparison A X.sheaf φ M N).val.app V)
          (tensorFunctor_map_unit_apply
            (N := (_root_.SheafOfModules.restrictScalars
              (underlyingRingHom (φ := φ))).obj N) c V q y))
        (laxComparison_val_app_tensorSheafUnit (φ := φ) M N V (c.val.app V q) y)
    exact Eq.trans (congrArg (fun t => (g.val.app V) t) e.symm)
      (congrArg (fun ψ => (ψ.val.app V).hom
      ((PresheafOfModules.tensorSheafUnit Q
        ((_root_.SheafOfModules.restrictScalars (underlyingRingHom (φ := φ))).obj N)).app V
        (q ⊗ₜ[A.obj.obj V] y))) hg)
  refine (cancel_epi (laxComparison A X.sheaf φ M N)).1 (Eq.trans ?_ (comp_zero).symm)
  refine Stacks.SheafOfModules.OnSpace.tensor_hom_ext
    (PresheafOfModules.ringedSpaceOfSheaf A) fun U x y => ?_
  exact Eq.trans (congrArg (g.val.app U)
      (laxComparison_val_app_tensorSheafUnit (φ := φ) M N U x y))
    (apply_toTensorSheafSection_eq_zero c hgen g hg0 U x y)

end AlgebraicGeometry.SheafOfModules

end
