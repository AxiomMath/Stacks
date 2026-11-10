module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Spaces.ClosedImmersionQC
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypePermanence
public import StacksFrontier.AlgebraicGeometry.Spaces.FormallySmooth.EtaleCovering
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfCoverings
public import StacksFrontier.AlgebraicGeometry.Spaces.Topologies.PhCoverings
public import StacksFrontier.AlgebraicGeometry.Topologies.HTopology.EtaleHComparison

/-!
# Étale coverings of algebraic spaces are ph coverings

Let `S` be a scheme contained in a big fppf site `B`. An étale covering of an algebraic space
over `S` (Stacks 041E) is a ph covering of it (Stacks 0DFG): base changing the family to an
affine scheme-valued point of the target and taking a scheme atlas of each base changed member
produces an étale covering of that affine scheme by schemes, and an étale covering of schemes
is refined by a standard ph covering.

## Main results

* `AlgebraicGeometry.Space.isPHCovering_of_isEtaleCovering`: the étale case of **Stacks
  0DFH**.
* `AlgebraicGeometry.StandardPHCovering.locallyOfFiniteType` and
  `AlgebraicGeometry.StandardPHCovering.pushforward_iso`: a member of a standard ph covering
  is locally of finite type, and the covering stays standard after post-composition with an
  isomorphism.
* `AlgebraicGeometry.exists_standardPHCovering_homOver_of_isAffine`: a ph covering of an
  affine scheme is refined by a standard ph covering of that scheme itself, rather than of its
  affine open `⊤`.

## Implementation notes

The étale case needs only the unconditional `AlgebraicGeometry.isPHCovering_of_etale`, so it is
proved here directly rather than through fppf coverings. The fppf case, and with it the
syntomic, smooth and Zariski cases, are proved in
`StacksFrontier.AlgebraicGeometry.Spaces.Topologies.FppfPhCoverings`, which imports this file for
the shared lemmas below; the five together are Stacks 0DFH, and the étale clause of the tag is
claimed here.

The members of the standard ph refinement are schemes, not objects of the big fppf site, so
they have to be put back into it: each is affine and maps to the affine test object by a
morphism locally of finite type, hence lies below the cutoff by
`AlgebraicGeometry.Scheme.size_le_of_locallyOfFiniteType`.

## References

* [Stacks Project, Tag 0DFH](https://stacks.math.columbia.edu/tag/0DFH)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry

universe u v

/-- Every member of a standard ph covering is locally of finite type: it is an open immersion
followed by a proper morphism. -/
theorem StandardPHCovering.locallyOfFiniteType {ι : Type v} {T : Scheme.{u}} [IsAffine T]
    {X : ι → Scheme.{u}} {f : ∀ i, X i ⟶ T} (hf : StandardPHCovering f) (i : ι) :
    LocallyOfFiniteType (f i) := by
  obtain ⟨U, g, j, hg, -, hj, -, hc⟩ := hf.exists_presentation
  have := hj i
  rw [← hc i]
  infer_instance

/-- A standard ph covering of an affine scheme stays standard after post-composition with an
isomorphism onto another affine scheme. -/
theorem StandardPHCovering.pushforward_iso {X Y : Scheme.{u}} [IsAffine X] [IsAffine Y]
    {ι : Type v} {Z : ι → Scheme.{u}} {f : ∀ i, Z i ⟶ X} (hf : StandardPHCovering f)
    (e : X ≅ Y) : StandardPHCovering (fun i ↦ f i ≫ e.hom) := by
  have : Finite ι := hf.finite
  obtain ⟨U, g, j, hg, hs, hj, hc, hw⟩ := hf.exists_presentation
  exact StandardPHCovering.of_presentation _ hf.isAffine (g ≫ e.hom) j inferInstance
    inferInstance hj hc fun i ↦ by
      simpa only [Category.assoc] using congrArg (fun q ↦ q ≫ e.hom) (hw i)

/-- A ph covering of an affine scheme `T` is refined, over the identity of `T`, by a standard
ph covering of `T`.

The defining condition of a ph covering gives a standard ph covering of the affine open `⊤` of
`T`; composing with the isomorphism `⊤ ≅ T` moves it onto `T`. -/
theorem exists_standardPHCovering_homOver_of_isAffine {T : Scheme.{u}} [IsAffine T]
    {I : Type v} {X : I → Scheme.{u}} {f : ∀ i, X i ⟶ T} (hf : IsPHCovering X f) :
    ∃ A : PreZeroHypercover.{u} T, StandardPHCovering A.f ∧
      Nonempty (A.HomOver ({ I₀ := I, X := X, f := f } : PreZeroHypercover.{v} T) (𝟙 T)) := by
  obtain ⟨A₀, hA₀, ⟨H⟩⟩ := hf.2 ⊤ (isAffineOpen_top T)
  have : IsAffine (⊤ : T.Opens).toScheme := isAffineOpen_top T
  refine ⟨A₀.pushforward T.topIso.hom, hA₀.pushforward_iso T.topIso,
    ⟨H.s₀, fun j ↦ H.h₀ j ≫ pullback.fst (f (H.s₀ j)) (⊤ : T.Opens).ι, fun j ↦ ?_⟩⟩
  have key : H.h₀ j ≫ pullback.snd (f (H.s₀ j)) (⊤ : T.Opens).ι = A₀.f j := H.w₀ j
  change (H.h₀ j ≫ pullback.fst (f (H.s₀ j)) (⊤ : T.Opens).ι) ≫ f (H.s₀ j) =
    (A₀.f j ≫ (⊤ : T.Opens).ι) ≫ 𝟙 T
  rw [Category.comp_id]
  exact (Category.assoc _ _ _).trans ((congrArg (H.h₀ j ≫ ·) pullback.condition).trans
    ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ (⊤ : T.Opens).ι) key)))

namespace Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A jointly surjective family of étale morphisms of the site is an étale covering of
algebraic spaces after Yoneda.** Étaleness of each member transfers by
`AlgebraicGeometry.Space.presheaf_yoneda_map_etale_iff` and
`AlgebraicGeometry.Space.isEtale_iff_presheaf_of_yoneda`, and joint surjectivity on the points
of the representing schemes transfers by
`AlgebraicGeometry.Space.jointlySurjective_yoneda_of_scheme`.

This is the converse of
`AlgebraicGeometry.Space.isEtaleCovering_yoneda_of_isCovering`, which reads an étale covering
of representables as an étale covering of the representing schemes. -/
theorem isEtaleCovering_yoneda_of_etale {I : Type v} {T : BigFppfOver B S hS}
    (U : I → BigFppfOver B S hS) (f : ∀ i, U i ⟶ T)
    (hetale : ∀ i, AlgebraicGeometry.Etale ((BigFppfOver.toScheme B S hS).map (f i)))
    (hsurj : ∀ x : (BigFppfOver.toScheme B S hS).obj T,
      ∃ i, ∃ y : (BigFppfOver.toScheme B S hS).obj (U i),
        (BigFppfOver.toScheme B S hS).map (f i) y = x) :
    IsEtaleCovering B S hS (fun i ↦ yoneda.obj (U i)) (fun i ↦ yoneda.map (f i)) :=
  ⟨isAlgebraicSpace_yoneda B S hS T, fun i ↦ isAlgebraicSpace_yoneda B S hS (U i),
    fun i ↦ (isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map (f i))).2
      ((presheaf_yoneda_map_etale_iff B S hS (f i)).2 (hetale i)),
    jointlySurjective_yoneda_of_scheme B S hS U f hsurj⟩

/-- **Every object of the big fppf site over `S` has an étale covering by affine objects.**
The family is the affine open cover of the underlying scheme, each member regarded as an object
over `S` by composing with the structure morphism; an open immersion is étale, and an affine
open cover is surjective on points, so
`AlgebraicGeometry.Space.isEtaleCovering_yoneda_of_etale` applies.

This is the form of `AlgebraicGeometry.BigFppfOver.exists_affine_etale_cover` that a descent
argument along étale coverings of algebraic spaces consumes: the covering condition is
`AlgebraicGeometry.Space.IsEtaleCovering` of Stacks 041E rather than membership of a sieve in
the fppf topology. -/
theorem exists_affine_isEtaleCovering_yoneda (U : BigFppfOver B S hS) :
    ∃ (I : Type u) (V : I → BigFppfOver B S hS) (π : ∀ i, V i ⟶ U),
      (∀ i, IsAffine ((BigFppfOver.toScheme B S hS).obj (V i))) ∧
      IsEtaleCovering B S hS (fun i ↦ yoneda.obj (V i)) (fun i ↦ yoneda.map (π i)) := by
  let c := ((BigFppfOver.toScheme B S hS).obj U).affineCover
  have hc (i : c.I₀) : B.Contains (c.X i) :=
    Scheme.size_lt_of_isOpenImmersion (c.f i) U.left.property
  let V (i : c.I₀) : BigFppfOver B S hS :=
    Over.mk (ObjectProperty.homMk (c.f i ≫ B.inclusion.map U.hom) : B.obj (hc i) ⟶ B.obj hS)
  let π (i : c.I₀) : V i ⟶ U := Over.homMk (ObjectProperty.homMk (c.f i)) rfl
  refine ⟨c.I₀, V, π, fun i ↦ inferInstanceAs (IsAffine (c.X i)),
    isEtaleCovering_yoneda_of_etale B S hS V π
      (fun i ↦ inferInstanceAs (AlgebraicGeometry.Etale (c.f i))) fun x ↦ ?_⟩
  have hx : x ∈ ⋃ i, Set.range (c.f i) := c.iUnion_range ▸ Set.mem_univ x
  exact Set.mem_iUnion.mp hx

/-- For an étale covering `f` of an algebraic space and an affine scheme-valued point `a` of
its target, scheme atlases `β i` of the base changes of the members along `a` give morphisms
`v i` of the site into the test object whose underlying morphisms of schemes form a ph covering
of it. -/
theorem exists_isPHCovering_of_isEtaleCovering_pullback {I : Type v}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, X i ⟶ F} (hf : IsEtaleCovering B S hS X f) (U : BigFppfOver B S hS)
    [IsAffine ((BigFppfOver.toScheme B S hS).obj U)] (a : yoneda.obj U ⟶ F) :
    ∃ (V : I → BigFppfOver B S hS) (β : ∀ i, yoneda.obj (V i) ⟶ pullback a (f i))
      (v : ∀ i, V i ⟶ U), (∀ i, yoneda.map (v i) = β i ≫ pullback.fst a (f i)) ∧
      _root_.AlgebraicGeometry.IsPHCovering (fun i ↦ (BigFppfOver.toScheme B S hS).obj (V i))
        (fun i ↦ (BigFppfOver.toScheme B S hS).map (v i)) := by
  set toSch := BigFppfOver.toScheme B S hS
  have hbc := isEtaleCovering_pullback B S hS a (isAlgebraicSpace_yoneda B S hS U) X f hf
  choose V β hβsurj hβetale using fun i ↦ (hbc.source_isAlgebraicSpace i).exists_atlas
  have hatlas (i : I) : IsEtaleCovering B S hS
      (fun _ : PUnit.{v + 1} ↦ yoneda.obj (V i)) (fun _ ↦ β i) :=
    isEtaleCovering_atlas B S hS (hbc.source_isAlgebraicSpace i) (hβsurj i) (hβetale i)
  have hcomp := isEtaleCovering_comp B S hS (fun _ : I ↦ PUnit.{v + 1})
    (fun i ↦ pullback a (f i)) (fun i ↦ pullback.fst a (f i))
    (fun i _ ↦ yoneda.obj (V i)) (fun i _ ↦ β i) hbc hatlas
  have hcov : IsEtaleCovering B S hS (fun i ↦ yoneda.obj (V i))
      (fun i ↦ β i ≫ pullback.fst a (f i)) :=
    IsEtaleCovering.reindex B S hS hcomp
      (σ := fun i : I ↦ (⟨i, PUnit.unit⟩ : (i : I) × PUnit.{v + 1}))
      (fun ij ↦ ⟨ij.1, rfl⟩)
  set v : ∀ i, V i ⟶ U := fun i ↦ yoneda.preimage (β i ≫ pullback.fst a (f i)) with hv
  have hvmap (i : I) : yoneda.map (v i) = β i ≫ pullback.fst a (f i) := by
    simp [hv]
  have hcov' : IsEtaleCovering B S hS (fun i ↦ yoneda.obj (V i))
      (fun i ↦ yoneda.map (v i)) := by
    simpa only [hvmap] using hcov
  have hetale (i : I) : AlgebraicGeometry.Etale (toSch.map (v i)) :=
    (presheaf_yoneda_map_etale_iff B S hS (v i)).1
      ((isEtale_iff_presheaf_of_yoneda B S hS (yoneda.map (v i))).1 (hcov'.etale i))
  have hsurj (x : toSch.obj U) : ∃ i, x ∈ Set.range (toSch.map (v i)).base :=
    exists_preimage_of_jointlySurjective_yoneda B S hS V U v hcov'.jointly_surjective x
  have hph : _root_.AlgebraicGeometry.IsPHCovering
      (fun i ↦ toSch.obj (V i)) (fun i ↦ toSch.map (v i)) :=
    isPHCovering_of_etale _ _ hsurj hetale
  exact ⟨V, β, v, hvmap, hph⟩

/-- **The étale case of Stacks 0DFH.** An étale covering of an algebraic space over `S` is a
ph covering of it.

Each member is locally of finite type because it is étale. For an affine scheme-valued point
`a` of the target, the family is base changed along `a` and each base changed member is
replaced by a scheme atlas of it; the resulting family of morphisms of representables is still
étale and jointly surjective, so the underlying family of morphisms of schemes is an étale
covering of the affine test scheme and is refined by a standard ph covering of it by
`AlgebraicGeometry.isPHCovering_of_etale`. The members of that refinement are affine and of
finite type over the test object, hence lie in the site, and the refinement morphisms compose
with the atlases and the fibre product projections to refine the original family over `a`. -/
@[stacks 0DFH "étale coverings"]
theorem isPHCovering_of_isEtaleCovering {I : Type v}
    {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {X : I → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    {f : ∀ i, X i ⟶ F} (hf : IsEtaleCovering B S hS X f) :
    IsPHCovering B S hS X f := by
  classical
  refine ⟨hf.target_isAlgebraicSpace, hf.source_isAlgebraicSpace,
    fun i ↦ isLocallyOfFiniteType_of_isEtale' B S hS (f i) (hf.etale i), ?_⟩
  intro U _ a
  obtain ⟨V, β, v, hvmap, hph⟩ := exists_isPHCovering_of_isEtaleCovering_pullback B S hS hf U a
  set toSch := BigFppfOver.toScheme B S hS
  obtain ⟨A, hA, ⟨H⟩⟩ := exists_standardPHCovering_homOver_of_isAffine hph
  have hsmall (j : A.I₀) : B.Contains (A.X j) := by
    have := hA.isAffine j
    have := hA.locallyOfFiniteType j
    exact (Scheme.size_le_of_locallyOfFiniteType (A.f j)).trans_lt U.left.property
  let Q : PreZeroHypercover.{u} U :=
    { I₀ := A.I₀
      X := fun j ↦ Over.mk ((ObjectProperty.homMk (A.f j) : B.obj (hsmall j) ⟶ U.left) ≫ U.hom)
      f := fun j ↦ Over.homMk (ObjectProperty.homMk (A.f j)) }
  refine ⟨Q, hA, ⟨?_⟩⟩
  have hQmap (j : A.I₀) : toSch.map (Q.f j) = A.f j := rfl
  have hw (j : A.I₀) : H.h₀ j ≫ toSch.map (v (H.s₀ j)) = A.f j := by
    simpa using H.w₀ j
  have hb (j : A.I₀) : ∃ b : Q.X j ⟶ V (H.s₀ j), toSch.map b = H.h₀ j := by
    refine ⟨Over.homMk (ObjectProperty.homMk (H.h₀ j)) ?_, rfl⟩
    apply ObjectProperty.hom_ext
    change H.h₀ j ≫ (V (H.s₀ j)).hom.hom = A.f j ≫ U.hom.hom
    have hfac : toSch.map (v (H.s₀ j)) ≫ U.hom.hom = (V (H.s₀ j)).hom.hom :=
      congrArg (fun q ↦ q.hom) (v (H.s₀ j)).w
    rw [← hfac, ← Category.assoc, hw j]
  choose b hbmap using hb
  refine ⟨H.s₀, fun j ↦ yoneda.map (b j) ≫ β (H.s₀ j) ≫ pullback.snd a (f (H.s₀ j)),
    fun j ↦ ?_⟩
  have hQv (j : A.I₀) : b j ≫ v (H.s₀ j) = Q.f j := by
    apply Functor.map_injective toSch
    rw [Functor.map_comp, hbmap, hQmap]
    exact hw j
  calc (yoneda.map (b j) ≫ β (H.s₀ j) ≫ pullback.snd a (f (H.s₀ j))) ≫ f (H.s₀ j)
      = (yoneda.map (b j) ≫ yoneda.map (v (H.s₀ j))) ≫ a := by
        simp only [hvmap, Category.assoc, pullback.condition]
    _ = yoneda.map (Q.f j) ≫ a := by rw [← Functor.map_comp, hQv j]

end Space

end AlgebraicGeometry

end
