module

public import Mathlib.AlgebraicGeometry.Morphisms.Affine
public import Mathlib.AlgebraicGeometry.Morphisms.Proper
public import StacksFrontier.AlgebraicGeometry.Topologies.Ph.StandardRefinementBind

/-!
# Finite coproducts of proper morphisms

A finite coproduct of proper morphisms with a common target is proper: if `g j : X j ⟶ T` is
proper for every member of a finite family, then so is
`CategoryTheory.Limits.Sigma.desc g : ∐ X ⟶ T`.

Properness is not local at the source, so `AlgebraicGeometry.IsZariskiLocalAtSource.sigmaDesc`
does not apply, and Mathlib carries no coproduct-stability statement for any morphism property
of schemes beyond that one. The three constituents of properness are therefore treated
separately.

## Main results

* `AlgebraicGeometry.universallyClosed_sigmaDesc`: a finite coproduct of universally closed
  morphisms is universally closed.
* `AlgebraicGeometry.isProper_sigmaDesc`: a finite coproduct of proper morphisms is proper.
* `AlgebraicGeometry.isProper_sigmaMap`: the coproduct of a finite family of proper morphisms,
  as a morphism between the two coproducts, is proper.
* `AlgebraicGeometry.StandardPHCovering.bind_of_sigma`: the disjoint-union case of Stacks 0DBF
  part (2): composing a standard ph covering of each member of a standard ph covering whose
  presenting proper surjection has source the *coproduct* of its members again gives a standard
  ph covering.

## Implementation notes

`AlgebraicGeometry.LocallyOfFiniteType` is local at the source, so that constituent is
immediate. For the other two, write `Sigma.desc g = Sigma.map g ≫ Sigma.desc (fun _ ↦ 𝟙 T)`.

* `AlgebraicGeometry.UniversallyClosed` is handled directly rather than through that
  factorisation. Pullbacks distribute over finite coproducts, because `Scheme` is finitary
  extensive (`CategoryTheory.FinitaryExtensive`), so any base change of `Sigma.desc g` is, up to
  isomorphism, the coproduct of the base changes of the `g j`. A set closed in a finite
  coproduct meets each summand in a closed set, and a *finite* union of closed sets is closed;
  this is `AlgebraicGeometry.isClosedMap_of_sigma`, and it is the only place finiteness of the
  index type is really used for this constituent.
* `AlgebraicGeometry.IsSeparated` is handled through the factorisation. The van Kampen property
  of finite coproducts identifies `g j` with the base change of `Sigma.map g` along
  `Sigma.ι _ j`, and separatedness is local at the target, which settles the first factor. The
  second factor `∐_{j} T ⟶ T` is an *affine* morphism — the preimage of an affine open `U` is
  the disjoint union of the finitely many copies of `U`, which is affine by
  `AlgebraicGeometry.IsAffineOpen.iSup_of_disjoint` — and affine morphisms are separated.

## References

* [Stacks Project, Tag 01W6](https://stacks.math.columbia.edu/tag/01W6)
* [Stacks Project, Tag 0DBF](https://stacks.math.columbia.edu/tag/0DBF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace

universe w v u

namespace AlgebraicGeometry

variable {ι : Type v} [Finite ι] {T : Scheme.{u}} {X : ι → Scheme.{u}}

/-- A morphism out of a finite coproduct of schemes is a closed map as soon as its restriction
to each summand is. Finiteness of the index type is essential: the image of a closed set is the
union over the summands of the images of its (closed) traces, and only a finite union of closed
sets is closed. -/
theorem isClosedMap_of_sigma {W : Scheme.{u}} {Z : ι → Scheme.{u}} (k : (∐ Z) ⟶ W)
    (hk : ∀ j, IsClosedMap (Sigma.ι Z j ≫ k).base) : IsClosedMap k.base := by
  intro C hC
  have key : k.base '' C = ⋃ j, (Sigma.ι Z j ≫ k).base '' ((Sigma.ι Z j).base ⁻¹' C) := by
    apply Set.eq_of_subset_of_subset
    · rintro _ ⟨y, hy, rfl⟩
      obtain ⟨j, x, rfl⟩ : ∃ (j : ι) (x : Z j), (Sigma.ι Z j).base x = y := by
        obtain ⟨x, hx⟩ := (sigmaOpenCover Z).covers y
        exact ⟨_, x, hx⟩
      exact Set.mem_iUnion.2 ⟨j, x, hy, by rw [Scheme.Hom.comp_apply]⟩
    · refine Set.iUnion_subset fun j => ?_
      rintro _ ⟨x, hx, rfl⟩
      exact ⟨_, hx, by rw [← Scheme.Hom.comp_apply]⟩
  rw [key]
  exact isClosed_iUnion_of_finite fun j => hk j _ (hC.preimage (Sigma.ι Z j).continuous)

/-- A finite coproduct of universally closed morphisms with a common target is universally
closed. -/
theorem universallyClosed_sigmaDesc (g : ∀ j, X j ⟶ T) [∀ j, UniversallyClosed (g j)] :
    UniversallyClosed (Sigma.desc g) := by
  rw [universallyClosed_eq]
  intro X' Y' i₁ i₂ f' H
  set P : ι → Scheme.{u} := fun j => pullback i₂ (g j)
  have key := IsUniversalColimit.isPullback_of_isColimit_left
    (FinitaryPreExtensive.isUniversal_finiteCoproducts (coproductIsCoproduct X))
    g (Sigma.desc g) i₂ (fun j => pullback.fst i₂ (g j)) (fun j => pullback.snd i₂ (g j))
    (fun j => IsPullback.of_hasPullback _ _) (coproductIsCoproduct P)
  set k := Cofan.IsColimit.desc (coproductIsCoproduct P) (fun j => pullback.fst i₂ (g j))
  let e := key.isoIsPullback _ _ H
  have he : e.hom ≫ f' = k := by simp [e, k]
  refine IsClosedMap.of_comp_surjective (Scheme.homeoOfIso e).surjective
    (Scheme.Hom.continuous _) ?_
  change IsClosedMap (e.hom ≫ f').base
  rw [he]
  refine isClosedMap_of_sigma _ fun j => ?_
  rw [show Sigma.ι P j ≫ k = pullback.fst i₂ (g j) from Cofan.IsColimit.fac _ _ _]
  exact Scheme.Hom.isClosedMap _

/-- A finite coproduct of morphisms that are locally of finite type is locally of finite type.
This holds for an arbitrary index type, since being locally of finite type is local at the
source. -/
theorem locallyOfFiniteType_sigmaDesc {ι : Type v} [Small.{u} ι] {X : ι → Scheme.{u}}
    (g : ∀ j, X j ⟶ T) [∀ j, LocallyOfFiniteType (g j)] :
    LocallyOfFiniteType (Sigma.desc g) :=
  HasRingHomProperty.instIsZariskiLocalAtSource.sigmaDesc fun _ => inferInstance

/-- The preimage of an open `U` under the codiagonal `∐_{j} T ⟶ T` of a family of copies of `T`
is the disjoint union of the copies of `U`. -/
theorem preimage_sigmaDesc_id (T : Scheme.{u}) (U : T.Opens) :
    (Sigma.desc (fun _ : ι => 𝟙 T)) ⁻¹ᵁ U = ⨆ j : ι, (Sigma.ι (fun _ : ι => T) j) ''ᵁ U := by
  have key : ∀ j : ι, (Sigma.ι (fun _ : ι => T) j) ''ᵁ U
      = (Sigma.ι (fun _ : ι => T) j).opensRange ⊓ (Sigma.desc (fun _ : ι => 𝟙 T)) ⁻¹ᵁ U := by
    intro j
    rw [← Scheme.Hom.image_preimage_eq_opensRange_inf]
    congr 1
    rw [← Scheme.Hom.comp_preimage, Sigma.ι_comp_desc]
    simp
  have hcov : ⨆ j : ι, (Sigma.ι (fun _ : ι => T) j).opensRange = ⊤ :=
    (sigmaOpenCover (fun _ : ι => T)).iSup_opensRange
  calc (Sigma.desc (fun _ : ι => 𝟙 T)) ⁻¹ᵁ U
      = (⨆ j : ι, (Sigma.ι (fun _ : ι => T) j).opensRange) ⊓
          (Sigma.desc (fun _ : ι => 𝟙 T)) ⁻¹ᵁ U := by rw [hcov, top_inf_eq]
    _ = ⨆ j : ι, (Sigma.ι (fun _ : ι => T) j) ''ᵁ U := by
        rw [iSup_inf_eq]
        exact iSup_congr fun j => (key j).symm

/-- The codiagonal `∐_{j} T ⟶ T` of a finite family of copies of `T` is an affine morphism: the
preimage of an affine open is a finite disjoint union of affine opens. -/
theorem isAffineHom_sigmaDesc_id (T : Scheme.{u}) :
    IsAffineHom (Sigma.desc (fun _ : ι => 𝟙 T)) := by
  refine ⟨fun U hU => ?_⟩
  rw [preimage_sigmaDesc_id]
  have hsub : ∀ j : ι, (Sigma.ι (fun _ : ι => T) j) ''ᵁ U
      ≤ (Sigma.ι (fun _ : ι => T) j).opensRange := by
    rintro j _ ⟨x, -, rfl⟩
    exact ⟨x, rfl⟩
  exact IsAffineOpen.iSup_of_disjoint (fun j => hU.image_of_isOpenImmersion _)
    fun j l hjl => (disjoint_opensRange_sigmaι (fun _ : ι => T) j l hjl).mono (hsub j) (hsub l)

/-- Each member of a finite family is the base change of the induced morphism of coproducts
along the corresponding coproduct inclusion of the target. This is the van Kampen property of
finite coproducts in `Scheme`. -/
theorem isPullback_sigmaMap {Y : ι → Scheme.{u}} (g : ∀ j, X j ⟶ Y j) (j : ι) :
    IsPullback (Sigma.ι X j) (g j) (Limits.Sigma.map g) (Sigma.ι Y j) := by
  have hvk := FinitaryExtensive.isVanKampen_finiteCoproducts (coproductIsCoproduct Y)
  have h2 := hvk (Cofan.mk (∐ X) (Sigma.ι X)) (Discrete.natTrans fun l => g l.as)
    (Limits.Sigma.map g) ?_ (NatTrans.Equifibered.of_discrete _)
  · exact h2.mp ⟨coproductIsCoproduct X⟩ ⟨j⟩
  · ext l
    obtain ⟨l⟩ := l
    simp

/-- The coproduct of a finite family of proper morphisms, viewed as a morphism `∐ X ⟶ ∐ Y`
between the coproducts, is proper. -/
theorem isProper_sigmaMap {Y : ι → Scheme.{u}} (g : ∀ j, X j ⟶ Y j) [∀ j, IsProper (g j)] :
    IsProper (Limits.Sigma.map g) := by
  have hg : ∀ j, IsProper (g j) := fun j => inferInstance
  refine IsZariskiLocalAtTarget.of_openCover (P := @IsProper) (sigmaOpenCover Y) fun j => ?_
  change IsProper (pullback.snd (Limits.Sigma.map g) (Sigma.ι Y j))
  rw [← MorphismProperty.cancel_left_of_respectsIso @IsProper
      (isPullback_sigmaMap g j).isoPullback.hom,
    (isPullback_sigmaMap g j).isoPullback_hom_snd]
  exact hg j

/-- `Sigma.desc g` factors as the induced morphism of coproducts followed by the codiagonal. -/
theorem sigmaDesc_eq_sigmaMap_comp (g : ∀ j, X j ⟶ T) :
    Sigma.desc g = Limits.Sigma.map g ≫ Sigma.desc (fun _ : ι => 𝟙 T) := by
  ext j
  simp

/-- **A finite coproduct of proper morphisms with a common target is proper.** -/
theorem isProper_sigmaDesc (g : ∀ j, X j ⟶ T) [∀ j, IsProper (g j)] :
    IsProper (Sigma.desc g) := by
  have h₁ : UniversallyClosed (Sigma.desc g) := universallyClosed_sigmaDesc g
  have h₂ : LocallyOfFiniteType (Sigma.desc g) := locallyOfFiniteType_sigmaDesc g
  have h₃ : IsSeparated (Sigma.desc g) := by
    rw [sigmaDesc_eq_sigmaMap_comp g]
    have := isProper_sigmaMap g
    have := isAffineHom_sigmaDesc_id (ι := ι) T
    infer_instance
  exact ⟨⟩

/-- A coproduct of surjective morphisms, viewed as a morphism between the coproducts, is
surjective. -/
theorem surjective_sigmaMap {ι : Type v} [Small.{u} ι] {X Y : ι → Scheme.{u}}
    (g : ∀ j, X j ⟶ Y j) [∀ j, Surjective (g j)] : Surjective (Limits.Sigma.map g) := by
  refine ⟨fun y => ?_⟩
  obtain ⟨j, b, rfl⟩ : ∃ (j : ι) (b : Y j), (Sigma.ι Y j).base b = y := by
    obtain ⟨b, hb⟩ := (sigmaOpenCover Y).covers y
    exact ⟨_, b, hb⟩
  obtain ⟨a, ha⟩ := (g j).surjective b
  refine ⟨(Sigma.ι X j).base a, ?_⟩
  rw [← Scheme.Hom.comp_apply, Limits.Sigma.ι_map, Scheme.Hom.comp_apply, ha]

/-- **The disjoint-union case of Stacks 0DBF part (2).** Let `T` be affine and let
`{U j ⟶ T}` be a standard ph covering presented by a proper surjection `p` whose source is the
*coproduct* `∐ U` of its members — that is, the presenting affine open covering of the source is
by pairwise disjoint opens. Then refining each member by a standard ph covering of it again
gives a standard ph covering of `T`.

No compactification of the second-stage presentations is needed: the coproduct of the proper
surjections presenting them is already proper over `∐ U`, by
`AlgebraicGeometry.isProper_sigmaMap`. This is why this case of Stacks 0DBF part (2) needs no
input from Chow's lemma, unlike the general case treated in
`AlgebraicGeometry.StandardPHCovering.of_comp_presentation`. -/
theorem StandardPHCovering.bind_of_sigma {J : Type v} [Finite J] {T : Scheme.{u}} [IsAffine T]
    {U : J → Scheme.{u}} (hU : ∀ j, IsAffine (U j)) (p : (∐ U) ⟶ T) (hp : IsProper p)
    (hp' : Surjective p) {I : J → Type w} {W : ∀ j, I j → Scheme.{u}}
    {F : ∀ j, ∀ i, W j i ⟶ U j} (hF : ∀ j, StandardPHCovering (F j)) :
    StandardPHCovering fun s : Σ j, I j => F s.1 s.2 ≫ Sigma.ι U s.1 ≫ p := by
  have : ∀ j, IsAffine (U j) := hU
  have hIfin : ∀ j, Finite (I j) := fun j => (hF j).finite
  have : Finite (Σ j, I j) := inferInstance
  choose V q k hq hq' hk hcover hcomp using fun j => (hF j).exists_presentation
  have : ∀ j, IsProper (q j) := hq
  have : ∀ j, Surjective (q j) := hq'
  have : ∀ j, ∀ i, IsOpenImmersion (k j i) := hk
  refine StandardPHCovering.of_comp_presentation _
    (fun s => (hF s.1).isAffine s.2) (fun s => k s.1 s.2 ≫ Sigma.ι V s.1)
    hp hp' (isProper_sigmaMap q) (surjective_sigmaMap q) (fun s => inferInstance) ?_ fun s => ?_
  · refine Set.eq_univ_iff_forall.mpr fun x => ?_
    obtain ⟨j, y, rfl⟩ : ∃ (j : J) (y : V j), (Sigma.ι V j).base y = x := by
      obtain ⟨y, hy⟩ := (sigmaOpenCover V).covers x
      exact ⟨_, y, hy⟩
    obtain ⟨i, z, hz⟩ := Set.mem_iUnion.mp (hcover j ▸ Set.mem_univ y)
    exact Set.mem_iUnion.mpr ⟨⟨j, i⟩, z, by rw [Scheme.Hom.comp_apply, hz]⟩
  · rw [Category.assoc, ← Category.assoc (Sigma.ι V s.1), Limits.Sigma.ι_map, Category.assoc,
      ← Category.assoc (k s.1 s.2), hcomp s.1 s.2]

end AlgebraicGeometry

end
