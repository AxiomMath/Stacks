module

public import StacksFrontier.CategoryTheory.Abelian.SmallSubcategory.Construction

/-! # Small abelian full subcategories of a big abelian category

Let `𝒜` be an abelian category whose objects form a class rather than a set, and let
`A : S → 𝒜` be a family of objects indexed by a set `S`. There is a full subcategory
`𝒜' ⊆ 𝒜` such that `Ob(𝒜')` is a set, `𝒜'` contains every `A s`, `𝒜'` is abelian, and the
inclusion `𝒜' ⥤ 𝒜` is additive and exact. This is the first assertion of Stacks 05PQ.

No hypothesis beyond `Abelian 𝒜` is used: in particular `𝒜` is *not* assumed to have enough
injectives. The variant of this statement in
`StacksFrontier.CategoryTheory.Abelian.SmallSubcategory`, which does assume enough injectives,
produces a subcategory that in addition has enough injectives (Stacks 0010); the closure
conditions used there are those of `HasAbelianClosureCore` below together with closure under
injective envelopes.

## Main results

* `HasAbelianClosureCore`: the closure conditions on an object property `P : ObjectProperty 𝒜`
  — a zero object, binary biproducts, kernels and cokernels — that make `P.FullSubcategory` an
  abelian full subcategory of `𝒜` with exact inclusion.
* `exists_abelian_closureCore`: every family `A : S → 𝒜` is contained in a small object
  property satisfying `HasAbelianClosureCore`.
* `exists_small_abelian_full_subcategory`: the first assertion of Stacks 05PQ.

## Implementation notes

Subcategories are described by object properties: `ObjectProperty 𝒜` is a predicate on `𝒜`,
`P.FullSubcategory` is the full subcategory it spans, and `P.ι : P.FullSubcategory ⥤ 𝒜` is the
fully faithful inclusion. "`Ob(𝒜')` is a set" becomes `Small.{max v w} P.FullSubcategory`, and
"exact" becomes the conjunction of `PreservesFiniteLimits P.ι` and
`PreservesFiniteColimits P.ι`.

`P` is deliberately *not* required to be closed under arbitrary isomorphisms ("replete"):
repleteness is incompatible with `Small.{max v w} P.FullSubcategory` in a big category.
Membership in the witnessing `P` is therefore by equality with an explicit generator rather
than up to isomorphism.

Because `P` is not replete, the abelian structure on `P.FullSubcategory` is obtained through
`createsLimitFullSubcategoryInclusion'`: a limit cone on `F ⋙ P.ι` whose chosen point lies in
`P` is *created* by `P.ι`. The canonical `kernel f`, `cokernel f`, `X ⊞ Y` and a zero object
all lie in `P`, so `P.ι` creates all finite limits and colimits and `P.FullSubcategory`
inherits the abelian structure from `𝒜`. Mathlib's `instAbelianFullSubcategory` cannot be
used: it demands the stronger `IsClosedUnder{Kernels, Cokernels, FiniteProducts}`, i.e. that
*every* isomorphic (co)limit point lies in `P`.

## References

* [Stacks Project, Tag 05PQ](https://stacks.math.columbia.edu/tag/05PQ)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v w u

variable {𝒜 : Type u} [Category.{v} 𝒜] [Abelian 𝒜]
variable {S : Type w}

/-- `HasAbelianClosureCore P` says that the object property `P` contains a zero object and is
closed under binary biproducts, kernels and cokernels — exactly the closure properties that
make `P.FullSubcategory` an abelian full subcategory of `𝒜` with exact inclusion.

`P` is *not* required to be closed under arbitrary isomorphisms ("replete"), since repleteness
is incompatible with `Small.{max v w} P.FullSubcategory` in a big category. -/
structure HasAbelianClosureCore (P : ObjectProperty 𝒜) : Prop where
  /-- `P` contains a zero object. -/
  has_zero : ∃ Z : 𝒜, IsZero Z ∧ P Z
  /-- `P` is closed under binary biproducts. -/
  closed_biprod : ∀ X Y : 𝒜, P X → P Y → P (X ⊞ Y)
  /-- `P` is closed under kernels. -/
  closed_kernel : ∀ {X Y : 𝒜} (f : X ⟶ Y), P X → P Y → P (kernel f)
  /-- `P` is closed under cokernels. -/
  closed_cokernel : ∀ {X Y : 𝒜} (f : X ⟶ Y), P X → P Y → P (cokernel f)

/-- Every family `A : S → 𝒜` is contained in a `max v w`-small object property with all the
closure properties of `HasAbelianClosureCore`. The witness is `AbClosureConstr.generated id A`,
the range of a stage-built carrier: membership is by *equality* with a generator,
`∃ g, carrier id A g = Y`, rather than up to isomorphism, and that is what keeps
`P.FullSubcategory` small. -/
theorem exists_abelian_closureCore (A : S → 𝒜) :
    ∃ (P : ObjectProperty 𝒜),
      HasAbelianClosureCore P ∧
      Small.{max v w} P.FullSubcategory ∧
      (∀ s, P (A s)) :=
  ⟨AbClosureConstr.generated id A,
    { has_zero := AbClosureConstr.has_zero id
      closed_biprod := AbClosureConstr.closed_biprod id
      closed_kernel := AbClosureConstr.closed_kernel id
      closed_cokernel := AbClosureConstr.closed_cokernel id },
    AbClosureConstr.small_fullSubcat id A, AbClosureConstr.contains_A id⟩

section Products

variable {𝒞 : Type u} [Category.{v} 𝒞] {α : Type}

/-- The product of a family indexed by an empty type is a terminal object. -/
noncomputable def isTerminalPiOfIsEmpty [IsEmpty α] (g : α → 𝒞) [HasProduct g] :
    IsTerminal (∏ᶜ g) :=
  isLimitEquivIsTerminalOfIsEmpty 𝒞 (limit.cone (Discrete.functor g)) (limit.isLimit _)

/-- If `W` is a product of `g ∘ Option.some`, then the biproduct `g none ⊞ W` is a product of
the family `g` indexed by `Option α`. -/
noncomputable def biprodIsoPiOption [HasZeroMorphisms 𝒞] (g : Option α → 𝒞) {W : 𝒞}
    [HasBinaryBiproduct (g none) W] [HasProduct g] [HasProduct (g ∘ Option.some)]
    (iW : W ≅ ∏ᶜ (g ∘ Option.some)) :
    g none ⊞ W ≅ ∏ᶜ g := by
  let t : Fan g := Fan.mk (g none ⊞ W)
    (fun b => Option.rec biprod.fst (fun i => biprod.snd ≫ iW.hom ≫ Pi.π (g ∘ some) i) b)
  have hlim : IsLimit t := by
    refine Fan.IsLimit.mk t
      (fun s => biprod.lift (s.proj none)
        ((Pi.lift (f := g ∘ some) (fun i => s.proj (some i))) ≫ iW.inv)) ?_ ?_
    · rintro s (_ | i) <;> simp [t]
    · intro s m hm
      refine biprod.hom_ext _ _ (by simpa [t] using hm none) ?_
      rw [biprod.lift_snd]
      refine (Iso.eq_comp_inv iW).mpr (limit.hom_ext fun j => ?_)
      simpa [t] using hm (some j.as)
  exact hlim.conePointUniqueUpToIso (productIsProduct g)

end Products

namespace HasAbelianClosureCore

variable {P : ObjectProperty 𝒜}

/-- An object property with an abelian closure contains a zero object. -/
theorem containsZero (h : HasAbelianClosureCore P) : P.ContainsZero :=
  ⟨h.has_zero⟩

/-- `P` is closed under finite biproducts up to isomorphism: any finite family of objects of
`P` has a product in `𝒜` isomorphic to an object of `P`. The proof is an induction on the
index type, using `has_zero` for the empty family and `closed_biprod` to adjoin one factor. -/
theorem exists_iso_biproduct (h : HasAbelianClosureCore P) {ι : Type} [Finite ι] (f : ι → 𝒜)
    (hf : ∀ i, P (f i)) :
    ∃ W : 𝒜, P W ∧ Nonempty (W ≅ ∏ᶜ f) := by
  classical
  cases nonempty_fintype ι
  revert f hf
  refine Fintype.induction_empty_option
    (P := fun α _ => ∀ (g : α → 𝒜), (∀ i, P (g i)) →
        ∃ W : 𝒜, P W ∧ Nonempty (W ≅ ∏ᶜ g)) ?_ ?_ ?_ ι
  · intro α β _ e IH g hg
    have : Fintype α := Fintype.ofEquiv β e.symm
    obtain ⟨W, hW, ⟨iW⟩⟩ := IH (g ∘ e) fun i => hg (e i)
    exact ⟨W, hW, ⟨iW ≪≫ Pi.whiskerEquiv e fun _ => Iso.refl _⟩⟩
  · intro g _
    obtain ⟨Z, hZ, hPZ⟩ := h.has_zero
    exact ⟨Z, hPZ, ⟨hZ.isoIsTerminal (isTerminalPiOfIsEmpty g)⟩⟩
  · intro α _ IH g hg
    obtain ⟨W, hW, ⟨iW⟩⟩ := IH (g ∘ Option.some) fun i => hg (Option.some i)
    exact ⟨g none ⊞ W, h.closed_biprod _ _ (hg none) hW, ⟨biprodIsoPiOption g iW⟩⟩

/-- `P.ι` creates finite limits. Finite products are created because a finite family in `P` has
a product isomorphic to an object of `P` (`exists_iso_biproduct`), and equalizers are created
because the equalizer of `f` and `g` is the kernel of `f - g`, which lies in `P` by
`closed_kernel`; the two are assembled by
`createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts`. -/
@[instance_reducible]
noncomputable def createsFiniteLimits_ι (h : HasAbelianClosureCore P) :
    CreatesFiniteLimits P.ι := by
  have hcfp : CreatesFiniteProducts P.ι := by
    refine CreatesFiniteProducts.mk' P.ι (fun J _ => ?_)
    refine ⟨fun {K} => ?_⟩
    obtain ⟨hW, hiW⟩ := (h.exists_iso_biproduct (fun i => (K ⋙ P.ι).obj ⟨i⟩)
      fun i => (K.obj ⟨i⟩).property).choose_spec
    exact createsLimitOfFullyFaithfulOfIso (F := P.ι) ⟨_, hW⟩
      (hiW.some ≪≫ (HasLimit.isoOfNatIso (Discrete.natIsoFunctor (F := K ⋙ P.ι))).symm)
  have hcpp : CreatesLimitsOfShape WalkingParallelPair P.ι := by
    refine ⟨fun {K} => ?_⟩
    set F := K ⋙ P.ι
    set f := F.map WalkingParallelPairHom.left
    set g := F.map WalkingParallelPairHom.right
    have hPdom : P (F.obj WalkingParallelPair.zero) := (K.obj _).property
    have hPcod : P (F.obj WalkingParallelPair.one) := (K.obj _).property
    have hforkc : IsLimit (Preadditive.forkOfKernelFork
        (KernelFork.ofι (kernel.ι (f - g)) (kernel.condition (f - g)))) :=
      Preadditive.isLimitForkOfKernelFork (kernelIsKernel (f - g))
    exact createsLimitOfFullyFaithfulOfIso (F := P.ι)
      ⟨kernel (f - g), h.closed_kernel (f - g) hPdom hPcod⟩
      (hforkc.conePointUniqueUpToIso (limit.isLimit (parallelPair f g)) ≪≫
        (HasLimit.isoOfNatIso (diagramIsoParallelPair F)).symm)
  exact createsFiniteLimitsOfCreatesEqualizersAndFiniteProducts P.ι

/-- Dually, `P.ι` creates finite colimits. Finite coproducts are created because a finite
family in `P` has a biproduct isomorphic to an object of `P` (`exists_iso_biproduct`) and in an
abelian category `⨁ ≅ ∐`, and coequalizers are created because the coequalizer of `f` and `g`
is the cokernel of `f - g`, which lies in `P` by `closed_cokernel`. -/
@[instance_reducible]
noncomputable def createsFiniteColimits_ι (h : HasAbelianClosureCore P) :
    CreatesFiniteColimits P.ι := by
  have hcfc : CreatesFiniteCoproducts P.ι := by
    refine ⟨fun J _ => ⟨fun {K} => ?_⟩⟩
    haveI : HasBiproduct (fun i => (K ⋙ P.ι).obj (⟨i⟩ : Discrete J)) :=
      HasBiproduct.of_hasProduct _
    obtain ⟨hW, hiW⟩ := (h.exists_iso_biproduct (fun i => (K ⋙ P.ι).obj ⟨i⟩)
      fun i => (K.obj ⟨i⟩).property).choose_spec
    exact createsColimitOfFullyFaithfulOfIso (F := P.ι) ⟨_, hW⟩
      (hiW.some ≪≫ (biproduct.isoProduct (fun i => (K ⋙ P.ι).obj ⟨i⟩)).symm ≪≫
        biproduct.isoCoproduct (fun i => (K ⋙ P.ι).obj ⟨i⟩) ≪≫
        (HasColimit.isoOfNatIso (Discrete.natIsoFunctor (F := K ⋙ P.ι))).symm)
  have hcpp : CreatesColimitsOfShape WalkingParallelPair P.ι := by
    refine ⟨fun {K} => ?_⟩
    set F := K ⋙ P.ι
    set f := F.map WalkingParallelPairHom.left
    set g := F.map WalkingParallelPairHom.right
    have hPdom : P (F.obj WalkingParallelPair.zero) := (K.obj _).property
    have hPcod : P (F.obj WalkingParallelPair.one) := (K.obj _).property
    have hcoforkc : IsColimit (Preadditive.coforkOfCokernelCofork
        (CokernelCofork.ofπ (cokernel.π (f - g)) (cokernel.condition (f - g)))) :=
      Preadditive.isColimitCoforkOfCokernelCofork (cokernelIsCokernel (f - g))
    exact createsColimitOfFullyFaithfulOfIso (F := P.ι)
      ⟨cokernel (f - g), h.closed_cokernel (f - g) hPdom hPcod⟩
      (hcoforkc.coconePointUniqueUpToIso (colimit.isColimit (parallelPair f g)) ≪≫
        (HasColimit.isoOfNatIso (diagramIsoParallelPair F)).symm)
  exact createsFiniteColimitsOfCreatesCoequalizersAndFiniteCoproducts P.ι

end HasAbelianClosureCore

/-- `P.FullSubcategory` carries an abelian structure. Since `P.ι` creates all finite limits and
colimits, the subcategory has them and is preadditive (its hom-groups are those of `𝒜`); the
coimage-to-image comparison is an isomorphism because `P.ι` is fully faithful and therefore
reflects it from `𝒜`, so `Abelian.ofCoimageImageComparisonIsIso` applies. -/
theorem nonempty_abelian_of_closureCore {P : ObjectProperty 𝒜}
    (h : HasAbelianClosureCore P) :
    Nonempty (Abelian P.FullSubcategory) := by
  have : CreatesFiniteLimits P.ι := h.createsFiniteLimits_ι
  have : CreatesFiniteColimits P.ι := h.createsFiniteColimits_ι
  have : HasFiniteLimits P.FullSubcategory :=
    hasFiniteLimits_of_hasLimitsLimits_of_createsFiniteLimits P.ι
  have : HasFiniteColimits P.FullSubcategory :=
    hasFiniteColimits_of_hasColimits_of_createsFiniteColimits P.ι
  have : PreservesFiniteLimits P.ι :=
    Limits.preservesFiniteLimits_of_createsFiniteLimits_and_hasFiniteLimits P.ι
  have : PreservesFiniteColimits P.ι :=
    Limits.preservesFiniteColimits_of_createsFiniteColimits_and_hasFiniteColimits P.ι
  have : ∀ {X Y : P.FullSubcategory} (f : X ⟶ Y),
      IsIso (Abelian.coimageImageComparison f) := by
    intro X Y f
    -- Reflect the isomorphism through the fully faithful `P.ι`.
    have : IsIso (P.ι.map (Abelian.coimageImageComparison f)) :=
      (Arrow.isIso_iff_isIso_of_isIso
        (Abelian.PreservesCoimageImageComparison.iso P.ι f).hom).mpr inferInstance
    exact isIso_of_reflects_iso (Abelian.coimageImageComparison f) P.ι
  exact ⟨Abelian.ofCoimageImageComparisonIsIso⟩

/-- The inclusion `P.ι` is left exact: it creates finite limits and `𝒜` has them, so it
preserves them. -/
theorem nonempty_preservesFiniteLimits_of_closureCore {P : ObjectProperty 𝒜}
    (h : HasAbelianClosureCore P) :
    Nonempty (PreservesFiniteLimits P.ι) := by
  have := h.createsFiniteLimits_ι
  exact ⟨Limits.preservesFiniteLimits_of_createsFiniteLimits_and_hasFiniteLimits P.ι⟩

/-- The inclusion `P.ι` is right exact: it creates finite colimits and `𝒜` has them, so it
preserves them. -/
theorem nonempty_preservesFiniteColimits_of_closureCore {P : ObjectProperty 𝒜}
    (h : HasAbelianClosureCore P) :
    Nonempty (PreservesFiniteColimits P.ι) := by
  have := h.createsFiniteColimits_ι
  exact ⟨Limits.preservesFiniteColimits_of_createsFiniteColimits_and_hasFiniteColimits P.ι⟩

/-- **Stacks 05PQ**, first assertion. Let `𝒜` be an abelian category — in particular one whose
objects form a class — and let `A : S → 𝒜` be a family of objects indexed by a set `S`. There
is an object property `P` whose full subcategory `𝒜' = P.FullSubcategory` has a set of objects,
contains every `A s`, and admits an abelian structure for which the inclusion `P.ι` is additive
and exact.

Nothing beyond `Abelian 𝒜` is assumed; compare
`exists_small_abelian_subcategory_with_enough_injectives` (Stacks 0010), which additionally
assumes `EnoughInjectives 𝒜` and produces a subcategory with enough injectives. -/
@[stacks 05PQ "the small abelian subcategory"]
theorem exists_small_abelian_full_subcategory (A : S → 𝒜) :
    ∃ (P : ObjectProperty 𝒜),
      Small.{max v w} P.FullSubcategory ∧
      (∀ s, P (A s)) ∧
      ∃ (_ : Abelian P.FullSubcategory),
        P.ι.Additive ∧
        Nonempty (PreservesFiniteLimits P.ι) ∧
        Nonempty (PreservesFiniteColimits P.ι) := by
  obtain ⟨P, hclos, hsmall, hA⟩ := exists_abelian_closureCore A
  refine ⟨P, hsmall, hA, ?_⟩
  -- Fix an abelian structure on the subcategory.
  let : Abelian P.FullSubcategory := (nonempty_abelian_of_closureCore hclos).some
  exact ⟨inferInstance, Functor.fullSubcategoryInclusion_additive P,
    nonempty_preservesFiniteLimits_of_closureCore hclos,
    nonempty_preservesFiniteColimits_of_closureCore hclos⟩
