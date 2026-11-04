module

public import StacksFrontier.AlgebraicGeometry.CoherenceCriteria.Basic
public import StacksFrontier.AlgebraicGeometry.CoherentTFAE.Basic
public import StacksFrontier.AlgebraicGeometry.Meromorphic.DenominatorQuasicoherent
public import StacksFrontier.AlgebraicGeometry.Modules.StalkSupport
public import StacksFrontier.AlgebraicGeometry.Modules.TensorStalkNaturality
public import StacksFrontier.AlgebraicGeometry.Divisors.TensorPower
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.MorphismVanishing
public import StacksFrontier.AlgebraicGeometry.Divisors.AssociatedPoints.EmbeddedCharacterization
public import StacksFrontier.AlgebraicGeometry.Divisors.Meromorphic.DenominatorsInclusion
public import StacksFrontier.CategoryTheory.Abelian.ImageDescent
public import StacksCore.Tactic.StacksAttribute

/-!
# The denominator ideal acting on a module

Let `X` be a scheme, `L` an invertible sheaf of `𝒪_X`-modules, `s` a meromorphic section of `L`
and `F` an `𝒪_X`-module. The ideal of denominators `I` of `s` acts on `F` through the canonical
map `I ⊗_{𝒪_X} F ⟶ F`, and the image `I · F` of that action carries two canonical maps: the
inclusion `I · F ⟶ F` and multiplication by `s`, `I · F ⟶ F ⊗_{𝒪_X} L`. Both cokernels are
supported on the union of the supports of `𝒪_X / I` and `L / s(I)`, which is a closed nowhere
dense subset of `X` by [Stacks, Tag 02P0]. This is [Stacks, Tag 02P2].

## Main definitions

* `AlgebraicGeometry.denominatorIdealTensorAction`: the action `I ⊗ F ⟶ F` of the denominator
  ideal on the module, obtained by tensoring the ideal inclusion with `F`.
* `AlgebraicGeometry.denominatorIdealSmul`: the product `I · F`, the image of that action.
* `AlgebraicGeometry.denominatorIdealSmulι`: the inclusion `I · F ⟶ F`, the map `1` of the
  source.
* `AlgebraicGeometry.denominatorIdealTensorMul`: multiplication by `s` on `I ⊗ F`, with values
  in `F ⊗ L`.
* `AlgebraicGeometry.denominatorIdealBadLocus`: the union of the supports of the two denominator
  cokernels.
* `AlgebraicGeometry.denominatorIdealSmulMul`: the second canonical map `I · F ⟶ F ⊗ L`,
  together with the identity that characterises it.

## Main results

* `AlgebraicGeometry.denominatorIdealBadLocus_isClosed` and
  `AlgebraicGeometry.denominatorIdealBadLocus_isNowhereDense`: the exceptional subset is closed
  and nowhere dense.
* `AlgebraicGeometry.denominatorIdealSmul_inclusion_mono` and
  `AlgebraicGeometry.denominatorIdealSmulMul_mono`: both canonical maps are injective.
* `AlgebraicGeometry.denominatorIdealSmul_inclusion_support` and
  `AlgebraicGeometry.denominatorIdealSmulMul_cokernel_support`: both cokernels are supported on
  the exceptional subset.
* `AlgebraicGeometry.denominatorIdeal_kernel_comp_eq_zero`: the two kernels
  `ker(I ⊗ F ⟶ F)` and `ker(I ⊗ F ⟶ F ⊗ L)` annihilate each other's morphism, which is what
  makes the second canonical map exist and be injective.
* `AlgebraicGeometry.notMem_denominatorIdealBadLocus_of_mem_associatedPoints`: no associated
  point of `F` lies in the exceptional subset.
* `AlgebraicGeometry.denominatorIdealTensorMul_cokernel_support`: the cokernel of multiplication
  by `s` on `I ⊗ F` is supported on the exceptional subset.

## Implementation notes

The product `I · F` is the image of the action map rather than a submodule chosen by hand, so
the inclusion is the image inclusion and is a monomorphism by construction; the action map
itself is the ideal inclusion tensored with `F`, followed by the left unit constraint of the
sheaf tensor product.

The cokernel support is computed on one stalk at a time. Taking stalks preserves colimits, so a
point misses the support of a cokernel exactly when the stalk map is surjective there
(`AlgebraicGeometry.Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel`);
surjectivity then survives tensoring by
`AlgebraicGeometry.surjective_stalkLinearMap_tensorRightMap`, composing with an isomorphism,
and passing to the second factor of a composite, which is all the argument uses.

The second canonical map is the descent of multiplication by `s` along the factorisation of the
action map through its image (`CategoryTheory.Abelian.imageDesc`), so what has to be proved is
the inclusion `ker(I ⊗ F ⟶ F) ⊆ ker(I ⊗ F ⟶ F ⊗ L)`; its injectivity needs the reverse
inclusion as well, and the two together are
`AlgebraicGeometry.denominatorIdeal_kernel_comp_eq_zero`. Both go through the associated points
of `F`: off the exceptional subset the stalk maps of `I ⟶ 𝒪_X` and of `I ⟶ L` are bijective, so
the stalk maps of both maps out of `I ⊗ F` are injective there; the associated points of a
coherent module of full support without embedded associated points are generic points of
irreducible components of `X` ([Stacks, Tag 05AL]) and so avoid a closed nowhere dense subset;
and a morphism into a quasi-coherent module vanishing on the stalks at the associated points of
that module is zero ([Stacks, Tag 0AVL]). For the map with values in `F ⊗ L` the last step is
applied after cancelling the invertible factor, which is why only the associated points of `F`
are ever used.

Closedness of the exceptional subset needs the two cokernels to be of finite type, hence the
invertible sheaf and the structure sheaf to be coherent; that is where local Noetherianness
enters. Regularity of `s` is used only for the second cokernel's nowhere denseness, so it is
not a hypothesis of the closedness statement, where the source assumes it.

## References

* [Stacks Project, Tag 02P2](https://stacks.math.columbia.edu/tag/02P2)
* [Stacks Project, Tag 02P0](https://stacks.math.columbia.edu/tag/02P0)
* [Stacks Project, Tag 05AL](https://stacks.math.columbia.edu/tag/05AL)
* [Stacks Project, Tag 0AVL](https://stacks.math.columbia.edu/tag/0AVL)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite

universe u

namespace AlgebraicGeometry

variable (X : Scheme.{u})

/-- The left unit constraint `𝒪_X ⊗ F ≅ F` of the sheaf tensor product on a scheme. -/
abbrev Scheme.Modules.tensorLeftUnitor (F : X.Modules) :
    Scheme.Modules.tensorObj (SheafOfModules.unit X.ringCatSheaf) F ≅ F :=
  Stacks.SheafOfModules.Invertible.tensorProductLeftUnitor X.sheaf.obj X.ringCatSheaf.property F

/-- The symmetry `M ⊗ N ≅ N ⊗ M` of the sheaf tensor product on a scheme. -/
abbrev Scheme.Modules.tensorBraiding (M N : X.Modules) :
    Scheme.Modules.tensorObj M N ≅ Scheme.Modules.tensorObj N M :=
  Stacks.SheafOfModules.Invertible.tensorProductBraiding X.sheaf.obj X.ringCatSheaf.property M N

variable (L F : X.Modules) (s : MeromorphicSection X.sheaf L)

/-- The action of the ideal of denominators of `s` on `F`: the ideal inclusion tensored with
`F`, followed by the left unit constraint. Its image is the product `I · F` of
[Stacks, Tag 02P2]. -/
def denominatorIdealTensorAction :
    Scheme.Modules.tensorObj (denominatorIdeal X L s) F ⟶ F :=
  Scheme.Modules.tensorRightMap (denominatorIdealι X L s) F ≫
    (Scheme.Modules.tensorLeftUnitor X F).hom

/-- The product `I · F` of the ideal of denominators of `s` and the module `F`: the image of the
action of `I` on `F`. -/
@[stacks 02P2 "the product of the denominator ideal and the module"]
def denominatorIdealSmul : X.Modules :=
  Abelian.image (denominatorIdealTensorAction X L F s)

/-- The first canonical map, the inclusion `I · F ⟶ F`. -/
@[stacks 02P2 "the first canonical map"]
def denominatorIdealSmulι : denominatorIdealSmul X L F s ⟶ F :=
  Abelian.image.ι (denominatorIdealTensorAction X L F s)

/-- Multiplication by the meromorphic section on `I ⊗ F`, with values in `F ⊗ L`: multiplication
by `s` on the ideal tensored with `F`, followed by the symmetry of the tensor product. The
second canonical map of [Stacks, Tag 02P2] is the map it induces on the product `I · F`. -/
def denominatorIdealTensorMul :
    Scheme.Modules.tensorObj (denominatorIdeal X L s) F ⟶ Scheme.Modules.tensorObj F L :=
  Scheme.Modules.tensorRightMap (denominatorIdealMul X L s) F ≫
    (Scheme.Modules.tensorBraiding X L F).hom

/-- The exceptional subset `T` of [Stacks, Tag 02P2]: the union of the supports of `𝒪_X / I` and
of `L / s(I)`, for `I` the ideal of denominators of `s`. -/
def denominatorIdealBadLocus : Set X :=
  SheafOfModules.supp (cokernel (denominatorIdealι X L s)) ∪
    SheafOfModules.supp (cokernel (denominatorIdealMul X L s))

/-- The exceptional subset is closed.

Both cokernels are quotients of modules of finite type — the structure sheaf and the invertible
sheaf `L`, both coherent on a locally Noetherian scheme — so both supports are closed.

Regularity of `s` is not used: the source assumes it throughout Tag 02P2, but of the
exceptional subset's two properties only nowhere denseness needs it. -/
@[stacks 02P2 "the exceptional subset is closed"]
theorem denominatorIdealBadLocus_isClosed [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property L) :
    IsClosed (denominatorIdealBadLocus X L s) := by
  have hLinv : Stacks.SheafOfModules.IsInvertible X.sheaf.obj X.ringCatSheaf.property L := by
    obtain ⟨G, hG, ⟨a⟩⟩ := hL.exists_tensorFunctor
    exact ⟨G, hG, ⟨⟨a.ι, a.bijective⟩⟩⟩
  have hLcoh := Stacks.AlgebraicGeometry.CoherenceCriteria.isCoherent_of_isInvertible X L
  have hLft : L.IsFiniteType :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent L).2
  have hOft : (SheafOfModules.unit X.ringCatSheaf).IsFiniteType :=
    Stacks.AlgebraicGeometry.CoherenceCriteria.isFiniteType_unit X
  exact (Scheme.Modules.isClosed_supp_cokernel (denominatorIdealι X L s) hOft).union
    (Scheme.Modules.isClosed_supp_cokernel (denominatorIdealMul X L s) hLft)

/-- The exceptional subset is nowhere dense: each of its two pieces is contained in a closed
nowhere dense subset by [Stacks, Tag 02P0]. -/
@[stacks 02P2 "the exceptional subset is nowhere dense"]
theorem denominatorIdealBadLocus_isNowhereDense
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s) :
    IsNowhereDense (denominatorIdealBadLocus X L s) := by
  obtain ⟨T₁, -, hT₁, h₁⟩ := denominatorIdeal_inclusion_support X L s hL
  obtain ⟨T₂, -, hT₂, h₂⟩ := denominatorIdeal_section_support X L s hL hs
  exact IsNowhereDense.mono (s := T₁ ∪ T₂) (Set.union_subset_union h₁ h₂) (hT₁.union hT₂)

/-- The first canonical map is injective: it is the inclusion of the image of the action map,
hence the kernel of a cokernel projection. -/
@[stacks 02P2 "injectivity of the first map"]
theorem denominatorIdealSmul_inclusion_mono : Mono (denominatorIdealSmulι X L F s) :=
  inferInstanceAs
    (Mono (kernel.ι (cokernel.π (denominatorIdealTensorAction X L F s))))

/-- The stalk map of a surjective-on-stalks morphism followed by an isomorphism is surjective. -/
private theorem surjective_stalkLinearMap_comp_hom {A B C : X.Modules} (f : A ⟶ B) (e : B ≅ C)
    (x : X) (hf : Function.Surjective (stalkLinearMap _ _ f x)) :
    Function.Surjective (stalkLinearMap _ _ (f ≫ e.hom) x) := by
  rw [show stalkLinearMap _ _ (f ≫ e.hom) x =
    stalkLinearMap _ _ e.hom x ∘ stalkLinearMap _ _ f x from
      funext (Scheme.Modules.stalkLinearMap_comp _ _ x)]
  exact (Scheme.Modules.surjective_stalkLinearMap_of_section _ e.inv e.inv_hom_id x).comp hf

/-- The cokernel of `f` is supported in `T` if the stalk map of `f` is surjective off `T`. -/
private theorem supp_cokernel_subset_of_surjective {A B : X.Modules} (f : A ⟶ B) {T : Set X}
    (h : ∀ x, x ∉ T → Function.Surjective (stalkLinearMap _ _ f x)) :
    SheafOfModules.supp (cokernel f) ⊆ T := fun x hx =>
  by_contra fun hnot =>
    ((Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel f x).1 (h x hnot)) hx

/-- The stalk map of the action of the denominator ideal on `F` is surjective at every point at
which the stalk map of the ideal inclusion is. -/
theorem surjective_stalkLinearMap_denominatorIdealTensorAction (x : X)
    (hι : Function.Surjective (stalkLinearMap _ _ (denominatorIdealι X L s) x)) :
    Function.Surjective (stalkLinearMap _ _ (denominatorIdealTensorAction X L F s) x) :=
  surjective_stalkLinearMap_comp_hom X _ (Scheme.Modules.tensorLeftUnitor X F) x
    (surjective_stalkLinearMap_tensorRightMap (denominatorIdealι X L s) F x hι)

/-- The cokernel of the first canonical map is supported on the exceptional subset.

Off the support of `𝒪_X / I` the stalk map of the ideal inclusion is surjective; tensoring with
`F` and composing with the left unit constraint keeps it so, and the action map factors through
`I · F`, so the stalk map of the inclusion `I · F ⟶ F` is surjective there as well. -/
@[stacks 02P2 "support of the first cokernel"]
theorem denominatorIdealSmul_inclusion_support :
    SheafOfModules.supp (cokernel (denominatorIdealSmulι X L F s)) ⊆
      denominatorIdealBadLocus X L s := by
  refine supp_cokernel_subset_of_surjective X _ fun x hnot => ?_
  have hι : Function.Surjective (stalkLinearMap _ _ (denominatorIdealι X L s) x) :=
    (Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel
      (denominatorIdealι X L s) x).2 fun h => hnot (Or.inl h)
  have hfac : Abelian.factorThruImage (denominatorIdealTensorAction X L F s) ≫
      denominatorIdealSmulι X L F s = denominatorIdealTensorAction X L F s :=
    Abelian.image.fac _
  refine Scheme.Modules.surjective_stalkLinearMap_of_comp
    (Abelian.factorThruImage (denominatorIdealTensorAction X L F s)) _ x ?_
  rw [hfac]
  exact surjective_stalkLinearMap_denominatorIdealTensorAction X L F s x hι

/-- The stalk map of multiplication by `s` on `I ⊗ F` is surjective at every point at which the
stalk map of multiplication by `s` on the ideal is. -/
theorem surjective_stalkLinearMap_denominatorIdealTensorMul (x : X)
    (hμ : Function.Surjective (stalkLinearMap _ _ (denominatorIdealMul X L s) x)) :
    Function.Surjective (stalkLinearMap _ _ (denominatorIdealTensorMul X L F s) x) :=
  surjective_stalkLinearMap_comp_hom X _ (Scheme.Modules.tensorBraiding X L F) x
    (surjective_stalkLinearMap_tensorRightMap (denominatorIdealMul X L s) F x hμ)

/-- The cokernel of multiplication by `s` on `I ⊗ F` is supported on the exceptional subset.
This is the content of the clause `support of the second cokernel` of [Stacks, Tag 02P2] before
the map is restricted to the product `I · F`: off the support of `L / s(I)` the stalk map of
multiplication by `s` on the ideal is surjective, and tensoring with `F` and composing with the
symmetry keeps it so. -/
theorem denominatorIdealTensorMul_cokernel_support :
    SheafOfModules.supp (cokernel (denominatorIdealTensorMul X L F s)) ⊆
      denominatorIdealBadLocus X L s := by
  refine supp_cokernel_subset_of_surjective X _ fun x hnot =>
    surjective_stalkLinearMap_denominatorIdealTensorMul X L F s x ?_
  exact (Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel
    (denominatorIdealMul X L s) x).2 fun h => hnot (Or.inr h)


/-- **No associated point of `F` lies in the exceptional subset.** For a coherent module of full
support without embedded associated points, every associated point is the generic point of an
irreducible component of the support, hence of `X` ([Stacks, Tag 05AL]); the exceptional subset
is closed and nowhere dense, and a generic point of an irreducible component of a locally
Noetherian scheme avoids every such subset. -/
theorem notMem_denominatorIdealBadLocus_of_mem_associatedPoints [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    [F.IsCoherent] (hF : AlgebraicGeometry.HasNoEmbeddedAssociatedPoints F)
    (hSupp : SheafOfModules.supp F = Set.univ)
    (x : X) (hx : x ∈ Stacks.Divisors.associatedPoints F) :
    x ∉ denominatorIdealBadLocus X L s := by
  have hg : ∃ Z ∈ irreducibleComponents (↥(SheafOfModules.supp F)),
      IsGenericPoint x (Subtype.val '' Z) := by
    by_contra h
    exact hF x ((isEmbeddedAssociatedPoint_iff_not_genericPoint X F x).2 ⟨hx, h⟩)
  rw [hSupp] at hg
  obtain ⟨Z, hZ, hxZ⟩ := hg
  have hZ' : Subtype.val '' Z ∈ irreducibleComponents X := by
    let e := Homeomorph.Set.univ X
    exact image_mem_irreducibleComponents_of_isPreirreducible_fiber e e.continuous e.isOpenMap
      (fun _ => Set.Subsingleton.isPreirreducible
        (fun a ha b hb => e.injective (ha.trans hb.symm))) e.surjective hZ
  exact Stacks.AlgebraicGeometry.CoherentSubquotients.genericPoint_notMem_of_nowhereDense X hZ' hxZ
    (denominatorIdealBadLocus_isClosed X L s hL)
    (denominatorIdealBadLocus_isNowhereDense X L s hL hs)

/-- The stalk map of the action of the denominator ideal on `F` is injective at every point at
which the stalk map of the ideal inclusion is bijective. -/
theorem injective_stalkLinearMap_denominatorIdealTensorAction (x : X)
    (hι : Function.Bijective (stalkLinearMap _ _ (denominatorIdealι X L s) x)) :
    Function.Injective (stalkLinearMap _ _ (denominatorIdealTensorAction X L F s) x) :=
  Scheme.Modules.injective_stalkLinearMap_comp
    (Scheme.Modules.tensorRightMap (denominatorIdealι X L s) F)
    (Scheme.Modules.tensorLeftUnitor X F).hom x
    (injective_stalkLinearMap_tensorRightMap (denominatorIdealι X L s) F x hι)
    (Scheme.Modules.injective_stalkLinearMap_of_retraction _
      (Scheme.Modules.tensorLeftUnitor X F).inv
      (Scheme.Modules.tensorLeftUnitor X F).hom_inv_id x)

/-- The stalk map of multiplication by `s` on `I ⊗ F` is injective at every point at which the
stalk map of multiplication by `s` on the ideal is bijective. -/
theorem injective_stalkLinearMap_denominatorIdealTensorMul (x : X)
    (hμ : Function.Bijective (stalkLinearMap _ _ (denominatorIdealMul X L s) x)) :
    Function.Injective (stalkLinearMap _ _ (denominatorIdealTensorMul X L F s) x) :=
  Scheme.Modules.injective_stalkLinearMap_comp
    (Scheme.Modules.tensorRightMap (denominatorIdealMul X L s) F)
    (Scheme.Modules.tensorBraiding X L F).hom x
    (injective_stalkLinearMap_tensorRightMap (denominatorIdealMul X L s) F x hμ)
    (Scheme.Modules.injective_stalkLinearMap_of_retraction _
      (Scheme.Modules.tensorBraiding X L F).inv
      (Scheme.Modules.tensorBraiding X L F).hom_inv_id x)

/-- **The two maps out of `I ⊗ F` have the same kernel.** Each of the action map and
multiplication by `s` kills the kernel of the other, so they have the same kernel as subobjects
of `I ⊗ F`.

At an associated point of `F` the stalk maps of both are injective, the point missing the
exceptional subset; hence the stalk map of either kernel inclusion vanishes there, and so does
the stalk map of the composite with the other morphism. A morphism into a quasi-coherent module
vanishing on the stalks at the associated points of that module is zero ([Stacks, Tag 0AVL]),
and for the composite with values in `F ⊗ L` the invertible factor is cancelled first. -/
theorem denominatorIdeal_kernel_comp_eq_zero [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    [F.IsCoherent] (hF : AlgebraicGeometry.HasNoEmbeddedAssociatedPoints F)
    (hSupp : SheafOfModules.supp F = Set.univ) :
    kernel.ι (denominatorIdealTensorAction X L F s) ≫ denominatorIdealTensorMul X L F s = 0 ∧
      kernel.ι (denominatorIdealTensorMul X L F s) ≫
        denominatorIdealTensorAction X L F s = 0 := by
  have _ := hL
  have hLqc : (L : X.Modules).IsQuasicoherent :=
    AlgebraicGeometry.isQuasicoherent_of_isInvertible L
  have hFqc : (F : X.Modules).IsQuasicoherent :=
    (Stacks.AlgebraicGeometry.CoherentTFAE.isQuasicoherent_isFiniteType_of_isCoherent F).1
  have hIqc : ((denominatorIdeal X L s : X.Modules)).IsQuasicoherent :=
    denominatorIdeal_isQuasicoherent X L s hL
  have _ := hFqc
  have hmι : Mono (denominatorIdealι X L s) :=
    Scheme.Modules.mono_of_right_cancellation _
      (fun g k hc => (denominatorIdeal_inclusion_mono X L s hL).right_cancellation g k hc)
  have hmμ : Mono (denominatorIdealMul X L s) :=
    Scheme.Modules.mono_of_right_cancellation _
      (fun g k hc => (denominatorIdeal_section_mono X L s hL hs).right_cancellation g k hc)
  have _ : (Scheme.Modules.tensorObj (denominatorIdeal X L s) F).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_tensorObj _ _ hIqc hFqc
  have _ : (Scheme.Modules.tensorObj F L).IsQuasicoherent :=
    Scheme.Modules.isQuasicoherent_tensorObj _ _ hFqc hLqc
  have _ : (kernel (denominatorIdealTensorAction X L F s)).IsQuasicoherent := inferInstance
  have _ : (kernel (denominatorIdealTensorMul X L F s)).IsQuasicoherent := inferInstance
  have key : ∀ x ∈ Stacks.Divisors.associatedPoints F,
      Function.Injective (stalkLinearMap _ _ (denominatorIdealTensorAction X L F s) x) ∧
        Function.Injective (stalkLinearMap _ _ (denominatorIdealTensorMul X L F s) x) := by
    intro x hx
    have hx' :=
      notMem_denominatorIdealBadLocus_of_mem_associatedPoints X L F s hL hs hF hSupp x hx
    exact ⟨injective_stalkLinearMap_denominatorIdealTensorAction X L F s x
        (Scheme.Modules.bijective_stalkLinearMap_of_notMem_supp_cokernel _ hmι x
          fun h => hx' (Or.inl h)),
      injective_stalkLinearMap_denominatorIdealTensorMul X L F s x
        (Scheme.Modules.bijective_stalkLinearMap_of_notMem_supp_cokernel _ hmμ x
          fun h => hx' (Or.inr h))⟩
  have hker : ∀ {A B C : X.Modules} (f : A ⟶ B) (g : A ⟶ C) (x : X),
      Function.Injective (stalkLinearMap _ _ f x) →
        (Scheme.Modules.stalkFunctor X x).map (kernel.ι f ≫ g) = 0 := by
    intro A B C f g x hf
    refine ((Scheme.Modules.stalkFunctor X x).map_comp _ _).trans ?_
    rw [Scheme.Modules.stalkFunctor_map_kernel_ι_eq_zero f x
      ((ModuleCat.mono_iff_injective _).2 hf)]
    exact zero_comp
  refine ⟨?_, ?_⟩
  · refine eq_zero_of_stalkLinearMap_eq_zero_on_associatedPoints_tensorInvertible
      (hLinv := hL) _ fun x hx => ?_
    exact (Scheme.Modules.stalkLinearMap_eq_zero_iff _ x).2 (hker _ _ x (key x hx).1)
  · exact eq_zero_of_stalkFunctor_map_eq_zero_on_associatedPoints _ fun x hx =>
      hker _ _ x (key x hx).2

/-- **The second canonical map `I · F ⟶ F ⊗ L`**, multiplication by the meromorphic section on
the product `I · F`, together with the identity characterising it: its composite with the
factorisation of the action map through its image is multiplication by `s` on `I ⊗ F`. Since that
factorisation is an epimorphism the identity determines the map, so this is the canonical map and
not an arbitrary one. -/
@[stacks 02P2 "the second canonical map"]
def denominatorIdealSmulMul [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    [F.IsCoherent] (hF : AlgebraicGeometry.HasNoEmbeddedAssociatedPoints F)
    (hSupp : SheafOfModules.supp F = Set.univ) :
    { f : denominatorIdealSmul X L F s ⟶ Scheme.Modules.tensorObj F L //
      Abelian.factorThruImage (denominatorIdealTensorAction X L F s) ≫ f =
        denominatorIdealTensorMul X L F s } :=
  ⟨Abelian.imageDesc (denominatorIdealTensorAction X L F s) (denominatorIdealTensorMul X L F s)
      (denominatorIdeal_kernel_comp_eq_zero X L F s hL hs hF hSupp).1,
    Abelian.factorThruImage_imageDesc _ _ _⟩

/-- The second canonical map is injective: the two maps out of `I ⊗ F` have the same kernel, so
the descents of each along the other's image factorisation are mutually inverse. -/
@[stacks 02P2 "injectivity of the second map"]
theorem denominatorIdealSmulMul_mono [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    [F.IsCoherent] (hF : AlgebraicGeometry.HasNoEmbeddedAssociatedPoints F)
    (hSupp : SheafOfModules.supp F = Set.univ) :
    Mono (denominatorIdealSmulMul X L F s hL hs hF hSupp).val :=
  Abelian.mono_imageDesc _ _
    (denominatorIdeal_kernel_comp_eq_zero X L F s hL hs hF hSupp).1
    (denominatorIdeal_kernel_comp_eq_zero X L F s hL hs hF hSupp).2

/-- The cokernel of the second canonical map is supported on the exceptional subset.

Off the support of `L / s(I)` the stalk map of multiplication by `s` on the ideal is surjective;
tensoring with `F` and composing with the symmetry keeps it so, and multiplication by `s` on
`I ⊗ F` factors through `I · F`, so the stalk map of the second canonical map is surjective
there as well. -/
@[stacks 02P2 "support of the second cokernel"]
theorem denominatorIdealSmulMul_cokernel_support [IsLocallyNoetherian X]
    (hL : AlgebraicGeometry.SheafOfModules.IsInvertible X.sheaf.obj
      X.ringCatSheaf.property L)
    (hs : IsRegularMeromorphicSection X.sheaf L s)
    [F.IsCoherent] (hF : AlgebraicGeometry.HasNoEmbeddedAssociatedPoints F)
    (hSupp : SheafOfModules.supp F = Set.univ) :
    SheafOfModules.supp (cokernel (denominatorIdealSmulMul X L F s hL hs hF hSupp).val) ⊆
      denominatorIdealBadLocus X L s := by
  refine supp_cokernel_subset_of_surjective X _ fun x hnot => ?_
  refine Scheme.Modules.surjective_stalkLinearMap_of_comp
    (Abelian.factorThruImage (denominatorIdealTensorAction X L F s)) _ x ?_
  rw [(denominatorIdealSmulMul X L F s hL hs hF hSupp).property]
  exact surjective_stalkLinearMap_denominatorIdealTensorMul X L F s x
    ((Scheme.Modules.surjective_stalkLinearMap_iff_notMem_supp_cokernel
      (denominatorIdealMul X L s) x).2 fun h => hnot (Or.inr h))

end AlgebraicGeometry

end
