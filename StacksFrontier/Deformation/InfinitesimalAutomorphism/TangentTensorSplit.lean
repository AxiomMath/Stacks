module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TangentTensor
public import StacksFrontier.Deformation.InfinitesimalAutomorphism.TensorAction

/-!
# Infinitesimal automorphisms as a torsor under the tangent space (Stacks 06JY)

Let `𝓕` be a category cofibered in groupoids over `𝒞_Λ` satisfying (RS), let `φ : x' ⟶ x` be
a morphism lying over a surjection `g : A' → A` whose kernel `I` is annihilated by the maximal
ideal of `A'`, and let `x₀` be a pushforward of `x` to the special fibre. Then `Inf(x'/x)`
carries a free and transitive action by `T_{id_{x₀}} Aut(x') ⊗_k I` (Stacks 06JY).

Write `x_I` for a pushforward of an (RS) fibre square of `x'` with itself over `x` along the
difference coordinate `(a₁, a₂) ↦ (ā₁, a₂ - a₁)`, and `x[I]` for the chosen pushforward of `x'`
to the square-zero extension `k ⊕ I` of the residue field. The two are isomorphic over
`k ⊕ I`.

## Main definitions

* `Deformation.kernelCoordinateModule`: the kernel `I` as a finite-dimensional vector space
  over the residue field, the coordinate module of the trivial extension.
* `Deformation.selfPullbackDiagonal`, `Deformation.kernelSplitInclusion`: the diagonal of the
  concrete self-fibre square of `g`, and the split inclusion `a ↦ (ā, 0)` it induces.
* `Deformation.kernelTrivialExtensionIso`,
  `Deformation.kernelTrivialExtensionUnderIso`: the identity on carriers, read as an
  isomorphism from the target of the difference coordinate to the square-zero extension by `I`
  under the base of `x'`.
* `Deformation.specialFibreUnderIso`: likewise for the residue field.
* `Deformation.chosenPushforwardComparison`: the comparison of an arbitrary pushforward with
  the chosen one.
* `Deformation.kernelSplitPushforwardIso`: **`x_I ≅ x[I]`**.

## Main results

* `Deformation.kernelSplitInclusion_comp_kernelTrivialExtensionIso`: the split inclusion is
  the structural arrow of the square-zero extension, so the two presentations of `k ⊕ I` agree
  *as objects under `A'`*.
* `Deformation.exists_isPullback_kernelTrivialExtension_diagonal`: the coordinate out of an
  arbitrary (RS) fibre square restricts along the diagonal to the split inclusion.
* `Deformation.relativeInfinitesimalAutomorphismsChosenMulEquiv`: the infinitesimal
  automorphisms of an arbitrary pushforward are those of the chosen one.
* `Deformation.exists_relativeInfinitesimalAutomorphisms_kernelSplitInclusion_action`: the
  free and transitive action of `Inf(x_I/x₀)`, together with the arrow `x' ⟶ x_I` over the
  split inclusion.
* `Deformation.exists_pushforwardIso_kernelTrivialExtension`: the isomorphism `x_I ≅ x[I]`
  over `k ⊕ I`.
* `Deformation.exists_freeTransitiveAction_tangentTensor_relativeInfinitesimalAutomorphisms`:
  **Stacks 06JY**, the free and transitive action of `T_{id_{x₀}} Aut(x') ⊗_k I` on
  `Inf(x'/x)`.

## Implementation notes

The target of `Deformation.infinitesimalDifferenceMap`, whose `Λ`-algebra structure comes from
`Λ → k`, and the square-zero extension under the base of `x'`, whose `Λ`-algebra structure
comes from `Λ → A' → k`, have the same carrier, ring and reduction but are distinct objects of
`𝒞_Λ`, because their structural algebra maps are only propositionally equal. They are compared
by `Deformation.kernelTrivialExtensionIso`, an isomorphism under `A'`
(`Deformation.kernelSplitInclusion_comp_kernelTrivialExtensionIso`); likewise
`Deformation.specialFibreUnderIso` for the residue field.

## References

* [Stacks Project, Tag 06IA](https://stacks.math.columbia.edu/tag/06IA)
* [Stacks Project, Tag 06JI](https://stacks.math.columbia.edu/tag/06JI)
* [Stacks Project, Tag 06JP](https://stacks.math.columbia.edu/tag/06JP)
* [Stacks Project, Tag 06JT](https://stacks.math.columbia.edu/tag/06JT)
* [Stacks Project, Tag 06JV](https://stacks.math.columbia.edu/tag/06JV)
* [Stacks Project, Tag 06JY](https://stacks.math.columbia.edu/tag/06JY)
-/

@[expose] public section

namespace Deformation

/-! ### The split inclusion into the trivial extension by the kernel -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]

/-- The kernel of a surjection of `𝒞_Λ` with annihilated kernel, as a finite-dimensional
vector space over the residue field: the coordinate module of the trivial extension. -/
public noncomputable abbrev kernelCoordinateModule
    {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : A' ⟶ A)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0) : FGModuleCat.{w} k :=
  letI := kernelModule f hann
  letI := kernelModule_finite f hann
  FGModuleCat.of k (RingHom.ker f.hom.toRingHom)

variable {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : A' ⟶ A)
  (hf : Function.Surjective f.hom)
  (hann : ∀ a : A', a ∈ maximalIdeal A' →
    ∀ i : RingHom.ker f.hom.toRingHom, a * (i : A') = 0)

/-- The diagonal of the concrete self-fibre square of a surjection of `𝒞_Λ`. -/
public noncomputable def selfPullbackDiagonal :
    A' ⟶ ArtinianLocalAlgCat.pullbackObj_of_surjective f f (.inl hf) :=
  (ArtinianLocalAlgCat.isPullback_of_surjective f f (.inl hf)).lift (𝟙 A') (𝟙 A') rfl

/-- The diagonal composed with the first projection is the identity. -/
public theorem selfPullbackDiagonal_comp_fst :
    selfPullbackDiagonal f hf ≫
        ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf) = 𝟙 A' :=
  (ArtinianLocalAlgCat.isPullback_of_surjective f f (.inl hf)).lift_fst (𝟙 A') (𝟙 A') rfl

/-- The diagonal composed with the second projection is the identity. -/
public theorem selfPullbackDiagonal_comp_snd :
    selfPullbackDiagonal f hf ≫
        ArtinianLocalAlgCat.pullbackSnd_of_surjective f f (.inl hf) = 𝟙 A' :=
  (ArtinianLocalAlgCat.isPullback_of_surjective f f (.inl hf)).lift_snd (𝟙 A') (𝟙 A') rfl

/-- The first coordinate of the diagonal is the identity. -/
public theorem selfPullbackDiagonal_fst (a : A') :
    (ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf)).hom
      ((selfPullbackDiagonal f hf).hom a) = a :=
  congrArg (fun q : A' ⟶ A' => q.hom a) (selfPullbackDiagonal_comp_fst f hf)

/-- The second coordinate of the diagonal is the identity. -/
public theorem selfPullbackDiagonal_snd (a : A') :
    (ArtinianLocalAlgCat.pullbackSnd_of_surjective f f (.inl hf)).hom
      ((selfPullbackDiagonal f hf).hom a) = a :=
  congrArg (fun q : A' ⟶ A' => q.hom a) (selfPullbackDiagonal_comp_snd f hf)

/-- **The split inclusion of `A'` into the trivial extension `k ⊕ I`.** It is the diagonal of
the self-fibre square followed by the difference coordinate, so it sends `a` to `(ā, 0)`. -/
public noncomputable def kernelSplitInclusion :
    A' ⟶ (infinitesimalDifferenceMap f hf hann).target :=
  selfPullbackDiagonal f hf ≫ (infinitesimalDifferenceMap f hf hann).g

/-- The first coordinate of the split inclusion is the residue. -/
public theorem kernelSplitInclusion_fst (a : A') :
    TrivSqZeroExt.fst ((kernelSplitInclusion f hf hann).hom a) =
      A'.residueEquiv (residue A' a) := by
  have h := (infinitesimalDifferenceMap f hf hann).first ((selfPullbackDiagonal f hf).hom a)
  rw [selfPullbackDiagonal_fst f hf a] at h
  exact h

/-- The second coordinate of the split inclusion is zero. -/
public theorem kernelSplitInclusion_snd (a : A') :
    TrivSqZeroExt.snd ((kernelSplitInclusion f hf hann).hom a) = 0 := by
  have h := (infinitesimalDifferenceMap f hf hann).second ((selfPullbackDiagonal f hf).hom a)
  refine Subtype.ext ?_
  change ((TrivSqZeroExt.snd ((kernelSplitInclusion f hf hann).hom a) :
    RingHom.ker f.hom.toRingHom) : A') = (0 : A')
  rw [show (TrivSqZeroExt.snd ((kernelSplitInclusion f hf hann).hom a) :
      RingHom.ker f.hom.toRingHom) =
    ((infinitesimalDifferenceMap f hf hann).coordinate
      ((infinitesimalDifferenceMap f hf hann).g.hom
        ((selfPullbackDiagonal f hf).hom a))).2 from rfl, h]
  change (ArtinianLocalAlgCat.pullbackSnd_of_surjective f f (.inl hf)).hom
      ((selfPullbackDiagonal f hf).hom a) -
    (𝟙 A' : A' ⟶ A').hom
      ((ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf)).hom
        ((selfPullbackDiagonal f hf).hom a)) = 0
  rw [selfPullbackDiagonal_snd f hf a]
  change _ - (ArtinianLocalAlgCat.pullbackFst_of_surjective f f (.inl hf)).hom
    ((selfPullbackDiagonal f hf).hom a) = 0
  rw [selfPullbackDiagonal_fst f hf a, sub_self]

/-- **The split inclusion read through an arbitrary fibre square.** For any fibre square of
`A'` with itself over `A` equipped with a diagonal, the difference coordinate makes the first
projection and a coordinate into the trivial extension `k ⊕ I` a fibre square over the
residue field, and that coordinate restricts along the diagonal to the split inclusion. -/
public theorem exists_isPullback_kernelTrivialExtension_diagonal
    {Y : ArtinianLocalAlgCat.{u, w, w} Λ k} {pr₁ pr₂ : Y ⟶ A'}
    (hPB : IsPullback pr₁ pr₂ f f) (d : A' ⟶ Y)
    (hd₁ : d ≫ pr₁ = 𝟙 A') (hd₂ : d ≫ pr₂ = 𝟙 A') :
    ∃ γ : Y ⟶ (infinitesimalDifferenceMap f hf hann).target,
      IsPullback pr₁ γ (residueMorphism A')
          (residueMorphism (infinitesimalDifferenceMap f hf hann).target) ∧
        d ≫ γ = kernelSplitInclusion f hf hann := by
  have hconc := ArtinianLocalAlgCat.isPullback_of_surjective f f (.inl hf)
  refine ⟨(hPB.isoIsPullback A' A' hconc).hom ≫ (infinitesimalDifferenceMap f hf hann).g,
    ?_, ?_⟩
  · refine (isPullback_infinitesimalMap f hf (infinitesimalDifferenceMap f hf hann)).of_iso'
      (hPB.isoIsPullback A' A' hconc) (Iso.refl _) (Iso.refl _) (Iso.refl _) ?_ ?_ ?_ ?_ <;> simp
  · have hd : d ≫ (hPB.isoIsPullback A' A' hconc).hom = selfPullbackDiagonal f hf := by
      refine hconc.hom_ext ?_ ?_ <;>
        simp [hd₁, hd₂, selfPullbackDiagonal_comp_fst, selfPullbackDiagonal_comp_snd]
    rw [← Category.assoc, hd]
    rfl

end

/-! ### The trivial extension as the split square-zero extension under the base -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k} {x : F}
  {A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : p.obj x ⟶ A)
  (hf : Function.Surjective f.hom)
  (hann : ∀ a : p.obj x, a ∈ maximalIdeal (p.obj x) →
    ∀ i : RingHom.ker f.hom.toRingHom, a * (i : p.obj x) = 0)

/-- The residue of a structural scalar is that scalar. -/
public theorem residueEquiv_residue_algebraMap
    (B : ArtinianLocalAlgCat.{u, w, w} Λ k) (t : Λ) :
    B.residueEquiv (residue B (algebraMap Λ B t)) = algebraMap Λ k t := by
  rw [show residue B (algebraMap Λ B t) = algebraMap Λ (ResidueField B) t by
    rw [IsScalarTower.algebraMap_apply Λ B (ResidueField B) t]
    simp [IsLocalRing.ResidueField.algebraMap_eq]]
  exact B.residueEquiv.commutes t

/-- The identity of `TrivSqZeroExt k I`, read as a morphism of `𝒞_Λ` from the target of the
difference coordinate to the square-zero extension under the base of `x`. -/
public noncomputable def kernelTrivialExtensionCompare :
    (infinitesimalDifferenceMap f hf hann).target ⟶
      (squareZeroUnder.{u, w, w, u₁, v₁} p x (kernelCoordinateModule f hann)).right where
  hom :=
    { toFun := fun z => z
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun t => by
        change TrivSqZeroExt.inl (algebraMap Λ k t) =
          TrivSqZeroExt.inl ((p.obj x).residueEquiv
            (residue (p.obj x) (algebraMap Λ (p.obj x) t)))
        rw [residueEquiv_residue_algebraMap (p.obj x) t] }
  isLocal := ⟨fun _ ha => ha⟩
  residue_comm := fun _ => rfl

/-- The comparison morphism is the identity on carriers. -/
public theorem kernelTrivialExtensionCompare_hom
    (z : (infinitesimalDifferenceMap f hf hann).target) :
    (kernelTrivialExtensionCompare.{u, w, u₁, v₁} (p := p) (x := x) f hf hann).hom z = z := rfl

/-- **The trivial extension `k ⊕ I` is the split square-zero extension under the base.** The
target of the difference coordinate is isomorphic, by the identity on carriers, to the
square-zero extension of the residue field by `I` read as an algebra under the base of `x`. -/
public noncomputable def kernelTrivialExtensionIso :
    (infinitesimalDifferenceMap f hf hann).target ≅
      (squareZeroUnder.{u, w, w, u₁, v₁} p x (kernelCoordinateModule f hann)).right :=
  isoOfBijectiveHom (kernelTrivialExtensionCompare.{u, w, u₁, v₁} (p := p) (x := x) f hf hann)
    ⟨fun _ _ h => h, fun z => ⟨z, rfl⟩⟩

/-- **The split inclusion is the structural arrow of the square-zero extension.** Composing
the split inclusion with the comparison isomorphism gives the canonical arrow from the base of
`x` into the square-zero extension by `I`. -/
public theorem kernelSplitInclusion_comp_kernelTrivialExtensionIso :
    kernelSplitInclusion f hf hann ≫
        (kernelTrivialExtensionIso.{u, w, u₁, v₁} (p := p) (x := x) f hf hann).hom =
      (squareZeroUnder.{u, w, w, u₁, v₁} p x (kernelCoordinateModule f hann)).hom := by
  refine ArtinianLocalAlgCat.hom_ext (AlgHom.ext fun a => ?_)
  simp only [ArtinianLocalAlgCat.comp_hom, AlgHom.comp_apply]
  rw [show (kernelTrivialExtensionIso.{u, w, u₁, v₁} (p := p) (x := x) f hf hann).hom.hom
      ((kernelSplitInclusion f hf hann).hom a) =
    (kernelSplitInclusion f hf hann).hom a from rfl]
  refine TrivSqZeroExt.ext ?_ ?_
  · rw [kernelSplitInclusion_fst f hf hann a]
    rfl
  · rw [kernelSplitInclusion_snd f hf hann a]
    rfl

/-- The split inclusion, read as an object under the base of `x`. -/
public noncomputable abbrev kernelTrivialExtensionUnder : Under (p.obj x) :=
  Under.mk (kernelSplitInclusion f hf hann)

/-- **The trivial extension and the square-zero extension agree under the base.** -/
public noncomputable def kernelTrivialExtensionUnderIso :
    kernelTrivialExtensionUnder.{u, w, u₁, v₁} (p := p) (x := x) f hf hann ≅
      squareZeroUnder.{u, w, w, u₁, v₁} p x (kernelCoordinateModule f hann) :=
  Under.isoMk (kernelTrivialExtensionIso.{u, w, u₁, v₁} (p := p) (x := x) f hf hann)
    (kernelSplitInclusion_comp_kernelTrivialExtensionIso.{u, w, u₁, v₁} (p := p) (x := x)
      f hf hann)

end

/-! ### The residue field under the base is the residue-field object -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k} (x : F)

/-- The identity of `ULift k`, read as a morphism of `𝒞_Λ` from the residue-field object to
the residue field regarded as an algebra under the base of `x`. -/
public noncomputable def specialFibreUnderCompare :
    residueFieldObject.{u, w, w} Λ k ⟶
      (specialFibreUnder.{u, w, w, u₁, v₁} (p := p) (x := x)).right where
  hom :=
    { toFun := fun z => z
      map_one' := rfl
      map_mul' := fun _ _ => rfl
      map_zero' := rfl
      map_add' := fun _ _ => rfl
      commutes' := fun t => by
        change ULift.up (algebraMap Λ k t) =
          ULift.up ((p.obj x).residueEquiv (residue (p.obj x) (algebraMap Λ (p.obj x) t)))
        rw [residueEquiv_residue_algebraMap (p.obj x) t] }
  isLocal := ⟨fun _ ha => ha⟩
  residue_comm := fun _ => rfl

/-- **The residue field under the base is the residue-field object of `𝒞_Λ`.** -/
public noncomputable def specialFibreUnderIso :
    residueFieldObject.{u, w, w} Λ k ≅
      (specialFibreUnder.{u, w, w, u₁, v₁} (p := p) (x := x)).right :=
  isoOfBijectiveHom (specialFibreUnderCompare.{u, w, u₁, v₁} (p := p) x)
    ⟨fun _ _ h => h, fun z => ⟨z, rfl⟩⟩

/-- Any two morphisms of `𝒞_Λ` into the residue field under the base agree. -/
public theorem hom_specialFibreUnder_right_ext
    {B : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (f₁ f₂ : B ⟶ (specialFibreUnder.{u, w, w, u₁, v₁} (p := p) (x := x)).right) : f₁ = f₂ := by
  have h : f₁ ≫ (specialFibreUnderIso.{u, w, u₁, v₁} (p := p) x).inv =
      f₂ ≫ (specialFibreUnderIso.{u, w, u₁, v₁} (p := p) x).inv :=
    hom_residueFieldObject_ext.{u, w, w} _ _
  calc f₁ = (f₁ ≫ (specialFibreUnderIso.{u, w, u₁, v₁} (p := p) x).inv) ≫
          (specialFibreUnderIso.{u, w, u₁, v₁} (p := p) x).hom := by
        rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]
    _ = (f₂ ≫ (specialFibreUnderIso.{u, w, u₁, v₁} (p := p) x).inv) ≫
          (specialFibreUnderIso.{u, w, u₁, v₁} (p := p) x).hom := by rw [h]
    _ = f₂ := by rw [Category.assoc, Iso.inv_hom_id, Category.comp_id]

end

/-! ### Comparing an arbitrary pushforward with the chosen one -/

section
open CategoryTheory IsLocalRing
universe u₂ v₂ u₁ v₁

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
  {p : F ⥤ C} {x : F} (P : ChosenPushforwardsAt p x)

/-- **The comparison of an arbitrary pushforward with the chosen one.** For `p` cofibered in
groupoids, an arrow `ι : x ⟶ y` lying over the structural arrow of an object `U` under
`p.obj x` gives an isomorphism of `y` with the chosen pushforward `P.obj U` in the fibre over
`U.right`. -/
public noncomputable def chosenPushforwardComparison (hp : IsCofiberedInGroupoids p)
    {U : Under (p.obj x)} {y : p.Fiber U.right} (ι : x ⟶ y.1)
    (hι : p.IsHomLift U.hom ι) : y ≅ P.obj U := by
  letI := isStronglyCocartesian_of_isCofiberedInGroupoids hp U.hom ι hι
  letI := P.inclusion_cocartesian U
  let m₁ := Functor.IsCocartesian.map p U.hom ι (P.inclusion U)
  let m₂ := Functor.IsCocartesian.map p U.hom (P.inclusion U) ι
  have h₁ : ι ≫ m₁ = P.inclusion U := Functor.IsCocartesian.fac p U.hom ι (P.inclusion U)
  have h₂ : P.inclusion U ≫ m₂ = ι := Functor.IsCocartesian.fac p U.hom (P.inclusion U) ι
  letI : p.IsHomLift (𝟙 U.right) (m₁ ≫ m₂) := by
    simpa using CategoryTheory.IsHomLift.comp p (𝟙 U.right) (𝟙 U.right) m₁ m₂
  letI : p.IsHomLift (𝟙 U.right) (m₂ ≫ m₁) := by
    simpa using CategoryTheory.IsHomLift.comp p (𝟙 U.right) (𝟙 U.right) m₂ m₁
  letI : p.IsHomLift (𝟙 U.right) (𝟙 y.1) := CategoryTheory.IsHomLift.id y.2
  letI : p.IsHomLift (𝟙 U.right) (𝟙 (P.obj U).1) := CategoryTheory.IsHomLift.id (P.obj U).2
  refine { hom := ⟨m₁, inferInstance⟩, inv := ⟨m₂, inferInstance⟩, hom_inv_id := ?_,
           inv_hom_id := ?_ }
  · refine Subtype.ext ?_
    change m₁ ≫ m₂ = 𝟙 y.1
    refine Functor.IsCocartesian.ext p U.hom ι _ _ ?_
    rw [← Category.assoc, h₁, h₂, Category.comp_id]
  · refine Subtype.ext ?_
    change m₂ ≫ m₁ = 𝟙 (P.obj U).1
    refine Functor.IsCocartesian.ext p U.hom (P.inclusion U) _ _ ?_
    rw [← Category.assoc, h₂, h₁, Category.comp_id]

/-- The comparison carries the given arrow from `x` to the chosen one. -/
public theorem chosenPushforwardComparison_fac (hp : IsCofiberedInGroupoids p)
    {U : Under (p.obj x)} {y : p.Fiber U.right} (ι : x ⟶ y.1)
    (hι : p.IsHomLift U.hom ι) :
    ι ≫ (chosenPushforwardComparison P hp ι hι).hom.val = P.inclusion U := by
  let _ := isStronglyCocartesian_of_isCofiberedInGroupoids hp U.hom ι hι
  let _ := P.inclusion_cocartesian U
  exact Functor.IsCocartesian.fac p U.hom ι (P.inclusion U)

end

/-! ### Infinitesimal automorphisms of an arbitrary pushforward -/

section
open CategoryTheory IsLocalRing
universe u₂ v₂ u₁ v₁

variable {F : Type u₁} [Category.{v₁} F] {C : Type u₂} [Category.{v₂} C]
  {p : F ⥤ C} {x : F} (P : ChosenPushforwardsAt p x)

/-- **The reduction arrow of an arbitrary pushforward is the chosen one, up to the
comparison.** The comparison isomorphisms over `U` and over `V` conjugate the given reduction
`fy` into the canonical arrow `P.map r` between the chosen pushforwards. -/
public theorem chosenPushforwardComparison_comp_map (hp : IsCofiberedInGroupoids p)
    {U V : Under (p.obj x)} (r : U ⟶ V)
    {y : p.Fiber U.right} {z : p.Fiber V.right}
    (ι : x ⟶ y.1) (hι : p.IsHomLift U.hom ι)
    (j : x ⟶ z.1) (hj : p.IsHomLift V.hom j)
    (fy : y.1 ⟶ z.1) (hfy : p.IsHomLift r.right fy) (hfac : ι ≫ fy = j) :
    (chosenPushforwardComparison P hp ι hι).hom.val ≫ P.map r =
      fy ≫ (chosenPushforwardComparison P hp j hj).hom.val := by
  let _ := isStronglyCocartesian_of_isCofiberedInGroupoids hp U.hom ι hι
  let _ := (chosenPushforwardComparison P hp ι hι).hom.2
  let _ := (chosenPushforwardComparison P hp j hj).hom.2
  let _ : p.IsHomLift r.right
      ((chosenPushforwardComparison P hp ι hι).hom.val ≫ P.map r) := by
    simpa using CategoryTheory.IsHomLift.comp p (𝟙 U.right) r.right
      (chosenPushforwardComparison P hp ι hι).hom.val (P.map r)
  let _ : p.IsHomLift r.right
      (fy ≫ (chosenPushforwardComparison P hp j hj).hom.val) := by
    simpa using CategoryTheory.IsHomLift.comp p r.right (𝟙 V.right) fy
      (chosenPushforwardComparison P hp j hj).hom.val
  refine Functor.IsStronglyCocartesian.ext p U.hom ι r.right ?_
  rw [← Category.assoc, ← Category.assoc, chosenPushforwardComparison_fac P hp ι hι,
    P.inclusion_map r, hfac, chosenPushforwardComparison_fac P hp j hj]

/-- **Transport of the kernel along an isomorphism under the base.** An isomorphism of
objects under `p.obj x` carries the kernel of the transport along `e.hom ≫ r` isomorphically
onto the kernel of the transport along `r`. -/
public noncomputable def kerTransportAutHomMulEquivOfIso {U U' V : Under (p.obj x)}
    (e : U ≅ U') (r : U' ⟶ V) :
    ↥(MonoidHom.ker (P.transportAutHom (e.hom ≫ r))) ≃*
      ↥(MonoidHom.ker (P.transportAutHom r)) := by
  have hleft : ∀ a : Aut (P.obj U),
      P.transportAutHom e.inv (P.transportAutHom e.hom a) = a := by
    intro a
    change P.transportAut e.inv (P.transportAut e.hom a) = a
    rw [← P.transportAut_comp, e.hom_inv_id, P.transportAut_id]
  have hright : ∀ b : Aut (P.obj U'),
      P.transportAutHom e.hom (P.transportAutHom e.inv b) = b := by
    intro b
    change P.transportAut e.hom (P.transportAut e.inv b) = b
    rw [← P.transportAut_comp, e.inv_hom_id, P.transportAut_id]
  have hiff : ∀ a : Aut (P.obj U), a ∈ MonoidHom.ker (P.transportAutHom (e.hom ≫ r)) ↔
      P.transportAutHom e.hom a ∈ MonoidHom.ker (P.transportAutHom r) := by
    intro a
    rw [MonoidHom.mem_ker, MonoidHom.mem_ker]
    change P.transportAut (e.hom ≫ r) a = 1 ↔
      P.transportAut r (P.transportAut e.hom a) = 1
    rw [P.transportAut_comp]
  refine
    { toFun := fun a => ⟨P.transportAutHom e.hom a.1, (hiff a.1).mp a.2⟩
      invFun := fun b => ⟨P.transportAutHom e.inv b.1, (hiff _).mpr ?_⟩
      left_inv := fun a => Subtype.ext (hleft a.1)
      right_inv := fun b => Subtype.ext (hright b.1)
      map_mul' := fun a b => Subtype.ext (map_mul (P.transportAutHom e.hom) a.1 b.1) }
  rw [hright]
  exact b.2

/-- **The infinitesimal automorphisms of an arbitrary pushforward are those of the chosen
one.** Let `r : U ⟶ V` be an arrow of objects under `p.obj x`, let `y` be an object of the
fibre over `U.right` receiving an arrow `ι` from `x` over the structural arrow of `U`, let
`fy : y ⟶ z` be a reduction of `y`, and let `t : z ⟶ P.obj V` be a monomorphism identifying
`z` with the chosen pushforward to `V` compatibly with `ι` and `fy`. Then conjugation by the
comparison isomorphism over `U` identifies the automorphisms of `y` trivial on `fy` with the
kernel of the transport of the chosen pushforwards along `r`. -/
public noncomputable def relativeInfinitesimalAutomorphismsChosenMulEquiv
    (hp : IsCofiberedInGroupoids p)
    {U V : Under (p.obj x)} (r : U ⟶ V)
    {y : p.Fiber U.right} {B : C} {z : p.Fiber B}
    (ι : x ⟶ y.1) (hι : p.IsHomLift U.hom ι)
    {q : U.right ⟶ B} (fy : y.1 ⟶ z.1) (hfy : p.IsHomLift q fy)
    (t : z.1 ⟶ (P.obj V).1) [Mono t]
    (hfz : p.IsHomLift r.right (fy ≫ t))
    (hfac : ι ≫ fy ≫ t = P.inclusion V) :
    ↥(relativeInfinitesimalAutomorphisms (x' := y) (x := z) hp q fy hfy) ≃*
      ↥(MonoidHom.ker (P.transportAutHom r)) := by
  let Θy := chosenPushforwardComparison P hp ι hι
  have hyi : Θy.inv.val ≫ Θy.hom.val = 𝟙 (P.obj U).1 :=
    congrArg Subtype.val Θy.inv_hom_id
  have hyh : Θy.hom.val ≫ Θy.inv.val = 𝟙 y.1 := congrArg Subtype.val Θy.hom_inv_id
  have hcomp : Θy.hom.val ≫ P.map r = fy ≫ t := by
    let _ := isStronglyCocartesian_of_isCofiberedInGroupoids hp U.hom ι hι
    let _ := Θy.hom.2
    let _ : p.IsHomLift r.right (Θy.hom.val ≫ P.map r) := by
      simpa using CategoryTheory.IsHomLift.comp p (𝟙 U.right) r.right Θy.hom.val (P.map r)
    refine Functor.IsStronglyCocartesian.ext p U.hom ι r.right ?_
    calc ι ≫ Θy.hom.val ≫ P.map r = (ι ≫ Θy.hom.val) ≫ P.map r :=
          (Category.assoc _ _ _).symm
      _ = P.inclusion U ≫ P.map r := by rw [chosenPushforwardComparison_fac P hp ι hι]
      _ = P.inclusion V := P.inclusion_map r
      _ = ι ≫ fy ≫ t := hfac.symm
  have hval : ∀ a : Aut y, (Θy.conjAut a).asIso.hom.val =
      Θy.inv.val ≫ a.asIso.hom.val ≫ Θy.hom.val := fun _ => rfl
  have hmemz : ∀ a : Aut y,
      (a.asIso.hom.val ≫ fy = fy) ↔ (a.asIso.hom.val ≫ fy ≫ t = fy ≫ t) := by
    intro a
    constructor
    · intro h
      rw [← Category.assoc, h]
    · intro h
      rw [← Category.assoc] at h
      exact (cancel_mono t).mp h
  have hiff : ∀ a : Aut y,
      a ∈ relativeInfinitesimalAutomorphisms (x' := y) (x := z) hp q fy hfy ↔
        Θy.conjAut a ∈ MonoidHom.ker (P.transportAutHom r) := by
    intro a
    rw [mem_relativeInfinitesimalAutomorphisms_iff, hmemz a,
      mem_ker_transportAutHom_iff, hval]
    constructor
    · intro h
      calc (Θy.inv.val ≫ a.asIso.hom.val ≫ Θy.hom.val) ≫ P.map r
          = Θy.inv.val ≫ a.asIso.hom.val ≫ Θy.hom.val ≫ P.map r := by
            simp only [Category.assoc]
        _ = Θy.inv.val ≫ a.asIso.hom.val ≫ fy ≫ t := by rw [hcomp]
        _ = Θy.inv.val ≫ fy ≫ t := by rw [h]
        _ = Θy.inv.val ≫ Θy.hom.val ≫ P.map r := by rw [hcomp]
        _ = (Θy.inv.val ≫ Θy.hom.val) ≫ P.map r := by rw [Category.assoc]
        _ = P.map r := by rw [hyi, Category.id_comp]
    · intro h
      have e1 : a.asIso.hom.val ≫ Θy.hom.val ≫ P.map r = Θy.hom.val ≫ P.map r := by
        calc a.asIso.hom.val ≫ Θy.hom.val ≫ P.map r
            = (Θy.hom.val ≫ Θy.inv.val) ≫ a.asIso.hom.val ≫ Θy.hom.val ≫ P.map r := by
              rw [hyh, Category.id_comp]
          _ = Θy.hom.val ≫ (Θy.inv.val ≫ a.asIso.hom.val ≫ Θy.hom.val) ≫ P.map r := by
              simp only [Category.assoc]
          _ = Θy.hom.val ≫ P.map r := by rw [h]
      rwa [← hcomp]
  refine
    { toFun := fun a => ⟨Θy.conjAut a.1, (hiff a.1).mp a.2⟩
      invFun := fun b => ⟨Θy.conjAut.symm b.1, (hiff _).mpr ?_⟩
      left_inv := fun a => ?_
      right_inv := fun b => ?_
      map_mul' := fun a b => ?_ }
  · rw [MulEquiv.apply_symm_apply]
    exact b.2
  · exact Subtype.ext (Θy.conjAut.symm_apply_apply a.1)
  · exact Subtype.ext (Θy.conjAut.apply_symm_apply b.1)
  · exact Subtype.ext (map_mul Θy.conjAut a.1 b.1)

end

/-! ### The action of the infinitesimal automorphisms of the split trivial extension -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k}

/-- **`x_I ≅ x[I]` over `k ⊕ I`.** Let `yI` be an object over the trivial extension
`k ⊕ I` receiving an arrow `ι` from `x` over the *split* inclusion `a ↦ (ā, 0)`. Then `yI` is
isomorphic to the chosen pushforward `x[I]` of `x` to the square-zero extension of the residue
field by `I`. The isomorphism lies over the identity-on-carriers comparison
`Deformation.kernelTrivialExtensionIso` of the two `Λ`-algebra structures on `k ⊕ I`, and it
carries `ι` to the canonical inclusion of `x` into `x[I]`. -/
public noncomputable def kernelSplitPushforwardIso (hp : IsCofiberedInGroupoids p)
    {x : F} {A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : p.obj x ⟶ A)
    (hf : Function.Surjective f.hom)
    (hann : ∀ a : p.obj x, a ∈ maximalIdeal (p.obj x) →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : p.obj x) = 0)
    (P : ChosenPushforwardsAt p x)
    {yI : p.Fiber (infinitesimalDifferenceMap f hf hann).target} (ι : x ⟶ yI.1)
    (hι : p.IsHomLift (kernelSplitInclusion f hf hann) ι) :
    yI.1 ≅ (P.obj (squareZeroUnder.{u, w, w, u₁, v₁} p x
      (kernelCoordinateModule f hann))).1 := by
  let ρ := kernelTrivialExtensionUnderIso.{u, w, u₁, v₁} (p := p) (x := x) f hf hann
  let Θ := chosenPushforwardComparison P hp
    (U := kernelTrivialExtensionUnder.{u, w, u₁, v₁} (p := p) (x := x) f hf hann) ι hι
  have hρ : P.map ρ.hom ≫ P.map ρ.inv =
      𝟙 (P.obj (kernelTrivialExtensionUnder.{u, w, u₁, v₁} (p := p) (x := x)
        f hf hann)).1 := by
    rw [← P.map_comp, ρ.hom_inv_id, P.map_id]
  have hρ' : P.map ρ.inv ≫ P.map ρ.hom =
      𝟙 (P.obj (squareZeroUnder.{u, w, w, u₁, v₁} p x (kernelCoordinateModule f hann))).1 := by
    rw [← P.map_comp, ρ.inv_hom_id, P.map_id]
  refine { hom := Θ.hom.val ≫ P.map ρ.hom, inv := P.map ρ.inv ≫ Θ.inv.val,
           hom_inv_id := ?_, inv_hom_id := ?_ }
  · calc (Θ.hom.val ≫ P.map ρ.hom) ≫ P.map ρ.inv ≫ Θ.inv.val
        = Θ.hom.val ≫ (P.map ρ.hom ≫ P.map ρ.inv) ≫ Θ.inv.val := by
          simp only [Category.assoc]
      _ = Θ.hom.val ≫ Θ.inv.val := by rw [hρ, Category.id_comp]
      _ = 𝟙 yI.1 := congrArg Subtype.val Θ.hom_inv_id
  · calc (P.map ρ.inv ≫ Θ.inv.val) ≫ Θ.hom.val ≫ P.map ρ.hom
        = P.map ρ.inv ≫ (Θ.inv.val ≫ Θ.hom.val) ≫ P.map ρ.hom := by
          simp only [Category.assoc]
      _ = P.map ρ.inv ≫ P.map ρ.hom := by
          rw [show Θ.inv.val ≫ Θ.hom.val = 𝟙 (P.obj
            (kernelTrivialExtensionUnder.{u, w, u₁, v₁} (p := p) (x := x) f hf hann)).1 from
            congrArg Subtype.val Θ.inv_hom_id, Category.id_comp]
      _ = _ := hρ'

/-- The isomorphism `x_I ≅ x[I]` carries the arrow over the split inclusion to the canonical
inclusion of `x` into its chosen pushforward. -/
public theorem kernelSplitPushforwardIso_fac (hp : IsCofiberedInGroupoids p)
    {x : F} {A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : p.obj x ⟶ A)
    (hf : Function.Surjective f.hom)
    (hann : ∀ a : p.obj x, a ∈ maximalIdeal (p.obj x) →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : p.obj x) = 0)
    (P : ChosenPushforwardsAt p x)
    {yI : p.Fiber (infinitesimalDifferenceMap f hf hann).target} (ι : x ⟶ yI.1)
    (hι : p.IsHomLift (kernelSplitInclusion f hf hann) ι) :
    ι ≫ (kernelSplitPushforwardIso.{u, w, u₁, v₁} hp f hf hann P ι hι).hom =
      P.inclusion (squareZeroUnder.{u, w, w, u₁, v₁} p x (kernelCoordinateModule f hann)) := by
  let U := kernelTrivialExtensionUnder.{u, w, u₁, v₁} (p := p) (x := x) f hf hann
  let ρ := kernelTrivialExtensionUnderIso.{u, w, u₁, v₁} (p := p) (x := x) f hf hann
  have h := chosenPushforwardComparison_fac P hp (U := U) ι hι
  calc ι ≫ (kernelSplitPushforwardIso.{u, w, u₁, v₁} hp f hf hann P ι hι).hom
      = (ι ≫ (chosenPushforwardComparison P hp (U := U) ι hι).hom.val) ≫ P.map ρ.hom :=
        (Category.assoc _ _ _).symm
    _ = P.inclusion U ≫ P.map ρ.hom := by rw [h]
    _ = P.inclusion (squareZeroUnder.{u, w, w, u₁, v₁} p x (kernelCoordinateModule f hann)) :=
        P.inclusion_map _

/-- The isomorphism `x_I ≅ x[I]` lies over the comparison of the two `Λ`-algebra structures
on `k ⊕ I`, that is, over the identity on carriers. -/
public theorem kernelSplitPushforwardIso_isHomLift (hp : IsCofiberedInGroupoids p)
    {x : F} {A : ArtinianLocalAlgCat.{u, w, w} Λ k} (f : p.obj x ⟶ A)
    (hf : Function.Surjective f.hom)
    (hann : ∀ a : p.obj x, a ∈ maximalIdeal (p.obj x) →
      ∀ i : RingHom.ker f.hom.toRingHom, a * (i : p.obj x) = 0)
    (P : ChosenPushforwardsAt p x)
    {yI : p.Fiber (infinitesimalDifferenceMap f hf hann).target} (ι : x ⟶ yI.1)
    (hι : p.IsHomLift (kernelSplitInclusion f hf hann) ι) :
    p.IsHomLift (kernelTrivialExtensionIso.{u, w, u₁, v₁} (p := p) (x := x) f hf hann).hom
      (kernelSplitPushforwardIso.{u, w, u₁, v₁} hp f hf hann P ι hι).hom := by
  let U := kernelTrivialExtensionUnder.{u, w, u₁, v₁} (p := p) (x := x) f hf hann
  let ρ := kernelTrivialExtensionUnderIso.{u, w, u₁, v₁} (p := p) (x := x) f hf hann
  let ϑ := kernelTrivialExtensionIso.{u, w, u₁, v₁} (p := p) (x := x) f hf hann
  have h1 : p.IsHomLift (𝟙 (infinitesimalDifferenceMap f hf hann).target)
      (chosenPushforwardComparison P hp (U := U) ι hι).hom.val :=
    (chosenPushforwardComparison P hp (U := U) ι hι).hom.2
  have hr : ρ.hom.right = ϑ.hom := rfl
  have h2 : p.IsHomLift ϑ.hom (P.map ρ.hom) := by
    rw [← hr]
    exact P.map_isHomLift _
  change p.IsHomLift _
    ((chosenPushforwardComparison P hp (U := U) ι hι).hom.val ≫ P.map ρ.hom)
  simpa using CategoryTheory.IsHomLift.comp p
    (𝟙 (infinitesimalDifferenceMap f hf hann).target) ϑ.hom
    (chosenPushforwardComparison P hp (U := U) ι hι).hom.val (P.map ρ.hom)

/-- The underlying map of a transport along an equality of objects of `𝒞_Λ` is surjective. -/
public theorem surjective_hom_eqToHom_of_eq {A B : ArtinianLocalAlgCat.{u, w, w} Λ k}
    (h : A = B) : Function.Surjective (eqToHom h).hom := by
  subst h
  exact fun b => ⟨b, rfl⟩

/-- **The free and transitive action of `Inf(x_I/x₀)`, with an arrow over the split
inclusion.** For a category cofibered in groupoids over `𝒞_Λ` satisfying (RS) and a morphism
`φ : x' ⟶ x` lying over a surjection whose kernel `I` is annihilated by the maximal ideal,
there are an object `x_I` over `k ⊕ I` with a reduction `x_I ⟶ x₀`, an arrow `x' ⟶ x_I` lying
over the split inclusion `A' ⟶ k ⊕ I` and compatible with the reductions to `x₀`, and a free
and transitive action of `Inf(x_I/x₀)` on `Inf(x'/x)`. -/
public theorem exists_relativeInfinitesimalAutomorphisms_kernelSplitInclusion_action
    (hrs : SatisfiesRS p) {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x' : p.Fiber A'} {x : p.Fiber A}
    (g : A' ⟶ A) (φ : x'.1 ⟶ x.1) (hφ : p.IsHomLift g φ)
    (hg : Function.Surjective g.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker g.hom.toRingHom, a * (i : A') = 0)
    {x₀ : p.Fiber (residueFieldObject.{u, w, w} Λ k)}
    (φ₀ : x'.1 ⟶ x₀.1) (hφ₀ : p.IsHomLift (residueMorphism A') φ₀) :
    ∃ (xI : p.Fiber (infinitesimalDifferenceMap g hg hann).target) (fI : xI.1 ⟶ x₀.1)
      (hfI : p.IsHomLift
        (residueMorphism (infinitesimalDifferenceMap g hg hann).target) fI)
      (ι : x'.1 ⟶ xI.1),
      p.IsHomLift (kernelSplitInclusion g hg hann) ι ∧ ι ≫ fI = φ₀ ∧
      ∃ act : ↥(relativeInfinitesimalAutomorphisms hrs.1
            (residueMorphism (infinitesimalDifferenceMap g hg hann).target) fI hfI) →
          ↥(relativeInfinitesimalAutomorphisms hrs.1 g φ hφ) →
          ↥(relativeInfinitesimalAutomorphisms hrs.1 g φ hφ),
        (∀ s, act 1 s = s) ∧
        (∀ a b s, act (a * b) s = act a (act b s)) ∧
        (∀ s, Function.Bijective fun a => act a s) := by
  obtain ⟨X', rfl⟩ := x'
  obtain ⟨X, rfl⟩ := x
  obtain rfl : g = p.map φ := IsHomLift.eq_of_isHomLift p g φ
  obtain ⟨cone, ⟨hlim⟩, ⟨hlimp⟩⟩ := hrs.2 φ φ hg
  have hsq : IsPullback cone.fst cone.snd φ φ := IsPullback.of_isLimit hlim
  have hbase0 : IsPullback (p.map cone.fst) (p.map cone.snd) (p.map φ) (p.map φ) :=
    IsPullback.of_isLimit hlimp
  let dF : X' ⟶ cone.pt := hsq.lift (𝟙 X') (𝟙 X') rfl
  have hdF₁ : dF ≫ cone.fst = 𝟙 X' := hsq.lift_fst (𝟙 X') (𝟙 X') rfl
  have hdF₂ : dF ≫ cone.snd = 𝟙 X' := hsq.lift_snd (𝟙 X') (𝟙 X') rfl
  have hd : ∀ {c : cone.pt ⟶ X'}, dF ≫ c = 𝟙 X' → p.map dF ≫ p.map c = 𝟙 (p.obj X') :=
    fun h => by rw [← p.map_comp, h, p.map_id]
  obtain ⟨γ, hbase, hdγ⟩ :=
    exists_isPullback_kernelTrivialExtension_diagonal (p.map φ) hg hann hbase0 (p.map dF)
      (hd hdF₁) (hd hdF₂)
  obtain ⟨XI, cI, hcI⟩ := exists_pushforward hrs.1 γ cone.pt rfl
  let xI : p.Fiber (infinitesimalDifferenceMap (p.map φ) hg hann).target :=
    ⟨XI, IsHomLift.codomain_eq p γ cI⟩
  let := IsHomLift.map p cone.fst
  let := isStronglyCocartesian_of_isCofiberedInGroupoids hrs.1 γ cI hcI
  let fI : XI ⟶ x₀.1 := Functor.IsStronglyCocartesian.map p γ cI hbase.w (cone.fst ≫ φ₀)
  have hfac : cI ≫ fI = cone.fst ≫ φ₀ :=
    Functor.IsStronglyCocartesian.fac p γ cI hbase.w (cone.fst ≫ φ₀)
  have hfI : p.IsHomLift
      (residueMorphism (infinitesimalDifferenceMap (p.map φ) hg hann).target) fI :=
    inferInstance
  have hbaseI : IsPullback (p.map cone.fst) (p.map cI) (p.map φ₀) (p.map fI) := by
    refine hbase.of_iso (Iso.refl _) (Iso.refl _) (eqToIso xI.2.symm) (eqToIso x₀.2.symm)
      ?_ ?_ ?_ ?_
    · simp
    · rw [IsHomLift.fac' p γ cI]; simp
    · rw [IsHomLift.fac' p (residueMorphism (p.obj X')) φ₀]; simp
    · rw [IsHomLift.fac' p
        (residueMorphism (infinitesimalDifferenceMap (p.map φ) hg hann).target) fI]
      simp
  have hsurjI : Function.Surjective (p.map fI).hom := by
    rw [IsHomLift.fac' p
      (residueMorphism (infinitesimalDifferenceMap (p.map φ) hg hann).target) fI]
    exact (surjective_hom_eqToHom_of_eq _).comp
      ((surjective_hom_residueMorphism _).comp (surjective_hom_eqToHom_of_eq _))
  obtain ⟨hlimI⟩ := isLimit_of_map_isLimit hrs φ₀ fI
    (PullbackCone.mk cone.fst cI hfac.symm) hsurjI
    ⟨IsLimit.ofIsoLimit hbaseI.isLimit
      (PullbackCone.ext (Iso.refl _) (Category.id_comp _).symm (Category.id_comp _).symm)⟩
  have hsqI : IsPullback cone.fst cI φ₀ fI := IsPullback.of_isLimit hlimI
  let E := relativeInfinitesimalAutomorphismsFibreSquareEquiv
    (z := ⟨cone.pt, rfl⟩) (x₁ := ⟨X', rfl⟩) (x₂ := xI) (x := x₀)
    hrs.1 (IsHomLift.map p cone.fst) hcI hfI hsqI hbase
  let := relativeInfinitesimalAutomorphismsFibreSquareAction
    (z := ⟨cone.pt, rfl⟩) (x₁ := ⟨X', rfl⟩) (x₂ := ⟨X', rfl⟩) (x := ⟨X, rfl⟩)
    hrs.1 (IsHomLift.map p cone.fst) (IsHomLift.map p cone.snd) (IsHomLift.map p φ) hsq hbase0
  have hbij := relativeInfinitesimalAutomorphismsFibreSquareAction_bijective
    (z := ⟨cone.pt, rfl⟩) (x₁ := ⟨X', rfl⟩) (x₂ := ⟨X', rfl⟩) (x := ⟨X, rfl⟩)
    hrs.1 (IsHomLift.map p cone.fst) (IsHomLift.map p cone.snd) (IsHomLift.map p φ) hsq hbase0
  have hιlift : p.IsHomLift (kernelSplitInclusion (p.map φ) hg hann) (dF ≫ cI) := by
    rw [← hdγ]
    exact IsHomLift.comp p (p.map dF) γ dF cI
  have hιfac : (dF ≫ cI) ≫ fI = φ₀ := by
    rw [Category.assoc, hfac, ← Category.assoc, hdF₁, Category.id_comp]
  refine ⟨xI, fI, hfI, dF ≫ cI, hιlift, hιfac,
    fun a s => (E.symm a) • s, fun s => ?_, fun a b s => ?_, fun s => ?_⟩
  · simp only [map_one]
    exact one_smul _ s
  · simp only [map_mul]
    exact mul_smul _ _ s
  · exact (hbij s).comp E.symm.bijective

/-- **The pushforward of the (RS) fibre square is the pushforward along the split inclusion,
`x_I ≅ x[I]` over `k ⊕ I`.** For a category cofibered in groupoids over
`𝒞_Λ` satisfying (RS) and a morphism `φ : x' ⟶ x` lying over a surjection whose kernel `I` is
annihilated by the maximal ideal, there is a pushforward `x_I` of an (RS) fibre square of `x'`
with itself over `x` to the trivial extension `k ⊕ I` which is isomorphic to the chosen
pushforward `x[I]` of `x'` to the square-zero extension of the residue field by `I`. The
isomorphism lies over the identity on carriers and carries the arrow `x' ⟶ x_I` over the split
inclusion to the canonical arrow `x' ⟶ x[I]`. -/
public theorem exists_pushforwardIso_kernelTrivialExtension
    (hrs : SatisfiesRS p) {X' : F} {A : ArtinianLocalAlgCat.{u, w, w} Λ k} {x : p.Fiber A}
    (g : p.obj X' ⟶ A) (φ : X' ⟶ x.1) (hφ : p.IsHomLift g φ)
    (hg : Function.Surjective g.hom)
    (hann : ∀ a : p.obj X', a ∈ maximalIdeal (p.obj X') →
      ∀ i : RingHom.ker g.hom.toRingHom, a * (i : p.obj X') = 0)
    (P : ChosenPushforwardsAt p X') :
    ∃ (xI : p.Fiber (infinitesimalDifferenceMap g hg hann).target) (ι : X' ⟶ xI.1)
      (_ : p.IsHomLift (kernelSplitInclusion g hg hann) ι)
      (e : xI.1 ≅ (P.obj (squareZeroUnder.{u, w, w, u₁, v₁} p X'
        (kernelCoordinateModule g hann))).1),
      p.IsHomLift (kernelTrivialExtensionIso.{u, w, u₁, v₁} (p := p) (x := X') g hg hann).hom
          e.hom ∧
        ι ≫ e.hom = P.inclusion (squareZeroUnder.{u, w, w, u₁, v₁} p X'
          (kernelCoordinateModule g hann)) := by
  obtain ⟨Y₀, ψ, hψ⟩ := exists_pushforward hrs.1 (residueMorphism (p.obj X')) X' rfl
  obtain ⟨xI, fI, hfI, ι, hι, -⟩ :=
    exists_relativeInfinitesimalAutomorphisms_kernelSplitInclusion_action
      hrs (x' := ⟨X', rfl⟩) g φ hφ hg hann
      (x₀ := ⟨Y₀, IsHomLift.codomain_eq p (residueMorphism (p.obj X')) ψ⟩) ψ hψ
  exact ⟨xI, ι, hι, kernelSplitPushforwardIso.{u, w, u₁, v₁} hrs.1 g hg hann P ι hι,
    kernelSplitPushforwardIso_isHomLift.{u, w, u₁, v₁} hrs.1 g hg hann P ι hι,
    kernelSplitPushforwardIso_fac.{u, w, u₁, v₁} hrs.1 g hg hann P ι hι⟩

end

/-! ### Stacks 06JY: the free and transitive action of the tangent space tensored with `I` -/

section
open CategoryTheory CategoryTheory.Limits IsLocalRing
universe u w u₁ v₁

variable {Λ : Type u} {k : Type w} [CommRing Λ] [Field k] [Algebra Λ k]
  {F : Type u₁} [Category.{v₁} F] {p : F ⥤ ArtinianLocalAlgCat.{u, w, w} Λ k}

/-- For a category cofibered in groupoids over `𝒞_Λ` satisfying (RS) and a morphism
`φ : x' ⟶ x` lying over a surjection `g : A' → A` whose kernel `I` is annihilated by the maximal
ideal of `A'`, the group `Inf(x'/x)` of infinitesimal automorphisms of `x'` over `x` carries a
free and transitive action by `T_{id_{x₀}} Aut(x') ⊗_k I`. -/
@[stacks 06JY "the free and transitive action"]
public theorem exists_freeTransitiveAction_tangentTensor_relativeInfinitesimalAutomorphisms
    (hrs : SatisfiesRS p) {A' A : ArtinianLocalAlgCat.{u, w, w} Λ k}
    {x' : p.Fiber A'} {x : p.Fiber A}
    (g : A' ⟶ A) (φ : x'.1 ⟶ x.1) (hφ : p.IsHomLift g φ)
    (hg : Function.Surjective g.hom)
    (hann : ∀ a : A', a ∈ maximalIdeal A' →
      ∀ i : RingHom.ker g.hom.toRingHom, a * (i : A') = 0)
    {x₀ : p.Fiber (residueFieldObject.{u, w, w} Λ k)}
    (ψ₀ : x.1 ⟶ x₀.1) (hψ₀ : p.IsHomLift (residueMorphism A) ψ₀)
    (P : ChosenPushforwardsAt p x'.1) :
    letI : Module k (RingHom.ker g.hom.toRingHom) := kernelModule g hann
    letI := naturalLocalizedTangentAddCommGroup P hrs
    letI := naturalLocalizedTangentModule P hrs
    ∃ act : TensorProduct k (localizedAutomorphismFunctorTangent P)
          (RingHom.ker g.hom.toRingHom) →
        ↥(relativeInfinitesimalAutomorphisms hrs.1 g φ hφ) →
        ↥(relativeInfinitesimalAutomorphisms hrs.1 g φ hφ),
      (∀ s, act 0 s = s) ∧
      (∀ t u s, act (t + u) s = act t (act u s)) ∧
      (∀ s t, act t s = s → t = 0) ∧
      (∀ s s', ∃ t, act t s = s') ∧
      (∀ s, Function.Bijective fun t => act t s) := by
  obtain ⟨X', rfl⟩ := x'
  let _ : Module k (RingHom.ker g.hom.toRingHom) := kernelModule g hann
  let _ := naturalLocalizedTangentAddCommGroup P hrs
  let _ := naturalLocalizedTangentModule P hrs
  have hres : g ≫ residueMorphism A = residueMorphism (p.obj X') :=
    eq_residueMorphism (g ≫ residueMorphism A)
  have hφ₀ : p.IsHomLift (residueMorphism (p.obj X')) (φ ≫ ψ₀) := by
    rw [← hres]
    exact CategoryTheory.IsHomLift.comp p g (residueMorphism A) φ ψ₀
  obtain ⟨xI, fI, hfI, ι, hι, hιfac, act, hone, hmul, hbij⟩ :=
    exists_relativeInfinitesimalAutomorphisms_kernelSplitInclusion_action
      hrs g φ hφ hg hann (φ ≫ ψ₀) hφ₀
  let M := kernelCoordinateModule g hann
  let red : squareZeroUnder.{u, w, w, u₁, v₁} p X' M ⟶
      specialFibreUnder.{u, w, w, u₁, v₁} (p := p) (x := X') :=
    squareZeroUnderRed.{u, w, w, u₁, v₁} p X' M
  let ρ := kernelTrivialExtensionUnderIso.{u, w, u₁, v₁} (p := p) (x := X') g hg hann
  let sI := specialFibreUnderIso.{u, w, u₁, v₁} (p := p) X'
  let _ : IsIso sI.hom := ⟨sI.inv, sI.hom_inv_id, sI.inv_hom_id⟩
  have hVhom : (specialFibreUnder.{u, w, w, u₁, v₁} (p := p) (x := X')).hom =
      residueMorphism (p.obj X') ≫ sI.hom :=
    hom_specialFibreUnder_right_ext X' _ _
  let _ := isStronglyCocartesian_of_isCofiberedInGroupoids hrs.1 (residueMorphism (p.obj X'))
    (φ ≫ ψ₀) hφ₀
  let _ := P.inclusion_cocartesian (specialFibreUnder.{u, w, w, u₁, v₁} (p := p) (x := X'))
  let t := Functor.IsStronglyCocartesian.map p (residueMorphism (p.obj X')) (φ ≫ ψ₀) hVhom
    (P.inclusion (specialFibreUnder.{u, w, w, u₁, v₁} (p := p) (x := X')))
  have htfac : (φ ≫ ψ₀) ≫ t =
      P.inclusion (specialFibreUnder.{u, w, w, u₁, v₁} (p := p) (x := X')) :=
    Functor.IsStronglyCocartesian.fac p (residueMorphism (p.obj X')) (φ ≫ ψ₀) hVhom
      (P.inclusion (specialFibreUnder.{u, w, w, u₁, v₁} (p := p) (x := X')))
  have htlift : p.IsHomLift sI.hom t := inferInstance
  let _ := isStronglyCocartesian_of_isCofiberedInGroupoids hrs.1 sI.hom t htlift
  have hti : IsIso t := Functor.IsStronglyCocartesian.isIso_of_base_isIso p sI.hom t
  have hfzlift : p.IsHomLift (ρ.hom ≫ red).right (fI ≫ t) := by
    rw [show (ρ.hom ≫ red).right =
        residueMorphism (infinitesimalDifferenceMap g hg hann).target ≫ sI.hom from
      hom_specialFibreUnder_right_ext X' _ _]
    exact CategoryTheory.IsHomLift.comp p
      (residueMorphism (infinitesimalDifferenceMap g hg hann).target) sI.hom fI t
  have hfacB : ι ≫ fI ≫ t =
      P.inclusion (specialFibreUnder.{u, w, w, u₁, v₁} (p := p) (x := X')) := by
    rw [← Category.assoc, hιfac, htfac]
  let B := relativeInfinitesimalAutomorphismsChosenMulEquiv P hrs.1 (ρ.hom ≫ red)
    (y := xI) (z := x₀) ι hι fI hfI t hfzlift hfacB
  let K := kerTransportAutHomMulEquivOfIso P ρ red
  obtain ⟨e₀, he₀⟩ :=
    exists_mulEquiv_tensor_infinitesimalAutomorphismKernel.{u, w, w, u₁, v₁} P hrs M
  let E := (B.toEquiv.trans K.toEquiv).trans e₀
  have he : ∀ a b, E (a * b) = E a + E b := by
    intro a b
    change e₀ (K (B (a * b))) = e₀ (K (B a)) + e₀ (K (B b))
    rw [map_mul B, map_mul K, he₀]
  have he1 : E 1 = 0 := by simpa using he 1 1
  have hzero : E.symm 0 = 1 := by
    rw [← he1, Equiv.symm_apply_apply]
  have hadd : ∀ t u, E.symm (t + u) = E.symm t * E.symm u := by
    intro t u
    apply E.injective
    rw [Equiv.apply_symm_apply, he, Equiv.apply_symm_apply, Equiv.apply_symm_apply]
  have h0 : ∀ s, act (E.symm 0) s = s := by
    intro s
    rw [hzero]
    exact hone s
  refine ⟨fun t s => act (E.symm t) s, ?_, ?_, ?_, ?_, ?_⟩
  · exact h0
  · intro t u s
    change act (E.symm (t + u)) s = act (E.symm t) (act (E.symm u) s)
    rw [hadd]
    exact hmul _ _ s
  · intro s t ht
    replace ht : act (E.symm t) s = s := ht
    exact E.symm.injective ((hbij s).1 (ht.trans (h0 s).symm))
  · intro s s'
    obtain ⟨a, ha⟩ := (hbij s).2 s'
    exact ⟨E a, (congrArg (act · s) (E.symm_apply_apply a)).trans ha⟩
  · exact fun s => (hbij s).comp E.symm.bijective

end

end Deformation

end
