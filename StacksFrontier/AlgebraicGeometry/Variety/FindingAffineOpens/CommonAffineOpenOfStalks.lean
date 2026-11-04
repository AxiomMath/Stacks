module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import Mathlib.AlgebraicGeometry.Morphisms.QuasiSeparated
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.AmpleCluster.QuasiAffineAndImmersion
public import StacksFrontier.AlgebraicGeometry.FibreDimension.IntegralReduction
public import StacksFrontier.AlgebraicGeometry.Limits.AffineFromSurjectiveUniversallyClosed
public import StacksFrontier.AlgebraicGeometry.Limits.RelativeApproximation.Basic
public import StacksFrontier.AlgebraicGeometry.Morphisms.Dominant.GenericPoints
public import StacksFrontier.AlgebraicGeometry.SchemeTheoreticImage.Reduced
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.LocalIsomorphism
public import StacksFrontier.AlgebraicGeometry.Variety.FindingAffineOpens.OpenImmersionCriterion
public import StacksFrontier.Topology.Irreducible.GenericPoints
public import StacksFrontier.Topology.Sober.Generization

/-!
# A finite family of points lying in a common affine open

Let `f : T ⟶ X` be a morphism from an affine scheme to a quasi-separated scheme with finitely
many generic points. If `f` carries the generic points of the irreducible components of `T`
injectively into those of `X`, and induces isomorphisms on the local rings at a finite family
of points of `T`, then the images of those points lie in a common affine open of `X`.

Both schemes may be replaced by their reductions: the induced morphism of reductions has the
same underlying map on points and the same local rings, and an affine open of the reduction of
`X` comes from an affine open of `X` because the inclusion of the reduction is a surjective
closed immersion. For reduced schemes, `T` is written as a limit of schemes of finite
presentation over `X` with affine transition maps, an affine stage `Y` is chosen, and `T` is
replaced by the scheme-theoretic image `Z` of `T ⟶ Y`, which is affine, reduced and of finite
type over `X` with `T ⟶ Z` dominant. Dominance and the injectivity hypothesis make
`𝒪_{X, x} ⟶ 𝒪_{Z, z} ⟶ 𝒪_{T, t}` a composition of isomorphisms, so `Z ⟶ X` is an open immersion
near each of the finitely many points, and the criterion for an open immersion on an open cover
of the source upgrades that to an open immersion on their union. A finite set of points of a
quasi-affine scheme lies in an affine open, whose image is the affine open sought.

## Main results

* `AlgebraicGeometry.exists_isAffineOpen_containing_image_of_genericPoints_injOn`: the common
  affine open.

## Implementation notes

The finite family of points is given as a function from an arbitrary finite type, and equality
of the local rings is expressed by asking that the canonical map of stalks be an isomorphism.
The conclusion concerns the images of exactly the points of that family.

## References

* [Stacks Project, Tag 09NI](https://stacks.math.columbia.edu/tag/09NI)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace

universe u v

namespace AlgebraicGeometry

/-- Every point of a quasi-sober space is a specialisation of the generic point of some
irreducible component. -/
private lemma exists_mem_genericPoints_specializes
    {A : Type u} [TopologicalSpace A] [QuasiSober A] (a : A) :
    ∃ η, η ∈ genericPoints A ∧ η ⤳ a := by
  let Z : irreducibleComponents A :=
    ⟨irreducibleComponent a, irreducibleComponent_mem_irreducibleComponents a⟩
  exact ⟨genericPoints.ofComponent Z, (genericPoints.ofComponent Z).2,
    (genericPoints.isGenericPoint_ofComponent Z).specializes mem_irreducibleComponent⟩

/-- A sober Kolmogorov space with finitely many generic points has finitely many irreducible
components, the two sets being in bijection. -/
private lemma finite_irreducibleComponents_of_finite_genericPoints
    {A : Type u} [TopologicalSpace A] [T0Space A] [QuasiSober A]
    (hA : (genericPoints A).Finite) : (irreducibleComponents A).Finite := by
  have : Finite (genericPoints A) := hA
  have : Finite (irreducibleComponents A) := Finite.of_equiv _ (genericPoints.equiv (α := A))
  exact Set.toFinite _

/-- The image of a point of the spectrum of a local ring of a scheme specializes to the point. -/
private lemma fromSpecStalk_specializes {X : Scheme.{u}} (x : X) (p : Spec (X.presheaf.stalk x)) :
    X.fromSpecStalk x p ⤳ x := by
  have : X.fromSpecStalk x p ∈ Set.range (X.fromSpecStalk x) := ⟨p, rfl⟩
  rwa [Scheme.range_fromSpecStalk] at this

/-- A point of the spectrum of a local ring of a scheme is a generic point exactly when its
image in the scheme is one: the canonical morphism from that spectrum is an embedding whose
range is the set of generizations of the point. -/
@[ega "I 7.2.8" "Case 1°, Lemma 7.2.8.1"]
private lemma fromSpecStalk_mem_genericPoints_iff {X : Scheme.{u}} (x : X)
    (y : Spec (X.presheaf.stalk x)) :
    y ∈ genericPoints (Spec (X.presheaf.stalk x)) ↔
      X.fromSpecStalk x y ∈ genericPoints X := by
  rw [mem_genericPoints_iff_forall_specializes_eq,
    mem_genericPoints_iff_forall_specializes_eq]
  have hf := (X.fromSpecStalk x).isEmbedding
  refine ⟨fun hy z hzy => ?_, fun hy z hzy => hf.injective (hy _ (hzy.map hf.continuous))⟩
  obtain ⟨w, rfl⟩ : z ∈ Set.range (X.fromSpecStalk x) := by
    rw [Scheme.range_fromSpecStalk]
    exact hzy.trans (fromSpecStalk_specializes x y)
  rw [hy w (hf.isInducing.specializes_iff.1 hzy)]

/-- The canonical map from the spectrum of a local ring is compatible with the induced map of
spectra of local rings. -/
private lemma fromSpecStalk_specMap_stalkMap {T X : Scheme.{u}} (f : T ⟶ X) (t : T)
    (q : Spec (T.presheaf.stalk t)) :
    X.fromSpecStalk (f t) (Spec.map (f.stalkMap t) q) = f (T.fromSpecStalk t q) :=
  congrArg (fun k : Spec (T.presheaf.stalk t) ⟶ X => k q)
    (Scheme.SpecMap_stalkMap_fromSpecStalk f)

/-- A generic point of the target which generizes the image of a point at which the map of local
rings is an isomorphism is the image of a generic point of the source generizing that point. -/
private lemma exists_mem_genericPoints_specializes_of_isIso_stalkMap
    {T X : Scheme.{u}} (f : T ⟶ X) (t : T)
    (hiso : IsIso (f.stalkMap t)) {θ : X} (hθ : θ ∈ genericPoints X)
    (hθt : θ ⤳ f t) :
    ∃ η : T, η ∈ genericPoints T ∧ η ⤳ t ∧ f η = θ := by
  obtain ⟨p, hp⟩ : θ ∈ Set.range (X.fromSpecStalk (f t)) := by
    rwa [Scheme.range_fromSpecStalk]
  have hpGeneric := (fromSpecStalk_mem_genericPoints_iff (f t) p).2 (by rwa [hp])
  let e : X.presheaf.stalk (f t) ≅ T.presheaf.stalk t := asIso (f.stalkMap t)
  let eSpec : Spec (X.presheaf.stalk (f t)) ≅ Spec (T.presheaf.stalk t) :=
    Scheme.Spec.mapIso e.symm.op
  have hp'Generic : eSpec.hom p ∈ genericPoints (Spec (T.presheaf.stalk t)) := by
    rw [← Scheme.homeoOfIso_apply eSpec p]
    exact (Homeomorph.mem_genericPoints_iff (Scheme.homeoOfIso eSpec) p).mpr hpGeneric
  let η : T := T.fromSpecStalk t (eSpec.hom p)
  have hback : Spec.map (f.stalkMap t) (eSpec.hom p) = p := by
    simp [eSpec, e, ← Scheme.Hom.comp_apply]
  refine ⟨η, (fromSpecStalk_mem_genericPoints_iff t (eSpec.hom p)).mp hp'Generic,
    fromSpecStalk_specializes t _, ?_⟩
  rw [← hp, ← hback, fromSpecStalk_specMap_stalkMap]

/-- The kernel of the map of local rings induced by a morphism at a point consists of
nilpotents as soon as every generic point generizing the image of the point is the image of a
generization of the point: the induced map of spectra then reaches every minimal prime. -/
theorem ker_stalkMap_le_nilradical_of_genericPoints {Y Z : Scheme.{u}} (φ : Y ⟶ Z) (y : Y)
    (h : ∀ θ ∈ genericPoints Z, θ ⤳ φ y → ∃ η, η ⤳ y ∧ φ η = θ) :
    RingHom.ker (φ.stalkMap y).hom ≤ nilradical (Z.presheaf.stalk (φ y)) := by
  refine (PrimeSpectrum.denseRange_comap_iff_ker_le_nilRadical _).mp ?_
  rw [PrimeSpectrum.denseRange_comap_iff_minimalPrimes]
  intro P hP
  let pz : Spec (Z.presheaf.stalk (φ y)) := ⟨P, hP.1.1⟩
  have hpGen : pz ∈ genericPoints (Spec (Z.presheaf.stalk (φ y))) := by
    refine (mem_genericPoints_iff_forall_specializes_eq pz).2 fun w hw => ?_
    have hpmin : pz.asIdeal ∈ minimalPrimes (Z.presheaf.stalk (φ y)) := hP
    exact (PrimeSpectrum.isMin_iff.mpr hpmin).eq_of_le
      ((PrimeSpectrum.le_iff_specializes w pz).2 hw)
  let θ : Z := Z.fromSpecStalk (φ y) pz
  obtain ⟨η, hηy, hηθ⟩ := h θ ((fromSpecStalk_mem_genericPoints_iff (φ y) pz).mp hpGen)
    (fromSpecStalk_specializes _ pz)
  obtain ⟨p', hp'⟩ : η ∈ Set.range (Y.fromSpecStalk y) := by
    rwa [Scheme.range_fromSpecStalk]
  refine ⟨p', ?_⟩
  show (Spec.map (φ.stalkMap y)) p' = pz
  apply (Z.fromSpecStalk (φ y)).isEmbedding.injective
  rw [fromSpecStalk_specMap_stalkMap, hp', hηθ]

/-- The kernel of the map of local rings induced by the inclusion of the reduction consists of
nilpotents: the induced map of spectra is dominant, because every generization of a point of the
reduction comes from a generization in the scheme. -/
private lemma ker_stalkMap_reductionι_le_nilradical {X : Scheme.{u}} (x : X.reduction) :
    RingHom.ker (X.reductionι.stalkMap x).hom ≤
      nilradical (X.presheaf.stalk (X.reductionι x)) := by
  let e : X.reduction ≃ₜ X := Scheme.reductionHomeo X
  have hsx : e.symm (X.reductionι x) = x := e.symm_apply_apply x
  exact ker_stalkMap_le_nilradical_of_genericPoints _ x fun θ _ hθx =>
    ⟨e.symm θ, by simpa only [hsx] using hθx.map e.symm.continuous, e.apply_symm_apply θ⟩

/-- In a commutative square of rings whose top map is bijective, whose vertical maps are
surjective, whose right vertical map has kernel contained in the nilradical, and whose bottom
left ring is reduced, the bottom map is bijective. -/
private lemma bijective_of_square_of_surjective
    {A B A' B' : Type u} [CommRing A] [CommRing B] [CommRing A'] [CommRing B']
    (α : A →+* B) (β : A →+* A') (γ : B →+* B') (δ : A' →+* B')
    (hα : Function.Bijective α) (hβ : Function.Surjective β)
    (hγ : Function.Surjective γ)
    (hker : RingHom.ker γ ≤ nilradical B) [_root_.IsReduced A']
    (hcomm : ∀ a, δ (β a) = γ (α a)) : Function.Bijective δ := by
  refine ⟨fun x y hxy => ?_, fun z => ?_⟩
  · obtain ⟨a, rfl⟩ := hβ x
    obtain ⟨b, rfl⟩ := hβ y
    have hγab : γ (α a) = γ (α b) := by rw [← hcomm, ← hcomm, hxy]
    have hnilB : α a - α b ∈ nilradical B := hker (by simp [RingHom.mem_ker, hγab])
    have hnilA : IsNilpotent (a - b) := by
      apply (IsNilpotent.map_iff hα.1).mp
      simpa only [map_sub] using (mem_nilradical.mp hnilB)
    rw [← sub_eq_zero, ← map_sub]
    exact isNilpotent_iff_eq_zero.mp (hnilA.map β)
  · obtain ⟨b, rfl⟩ := hγ z
    obtain ⟨a, rfl⟩ := hα.2 b
    exact ⟨β a, hcomm a⟩

/-- For a commutative square of schemes, the two composite maps of local rings at a point of the
top left corner agree once the two stalks at its image in the bottom right corner are
identified. -/
private lemma stalkSpecializes_comp_stalkMap_comp_of_comp_eq {X Y Y' S : Scheme.{u}}
    {f₀ : X ⟶ Y} {rY : Y ⟶ S} {rX : X ⟶ Y'} {f : Y' ⟶ S} (hfac : f₀ ≫ rY = rX ≫ f) (x : X)
    (hpoint : rY (f₀ x) = f (rX x)) :
    (S.presheaf.stalkSpecializes (Inseparable.of_eq hpoint.symm).ge ≫ rY.stalkMap (f₀ x)) ≫
      f₀.stalkMap x = f.stalkMap (rX x) ≫ rX.stalkMap x := by
  let κ := S.presheaf.stalkSpecializes (Inseparable.of_eq hpoint.symm).ge
  have hh' : κ ≫ (f₀ ≫ rY).stalkMap x = (rX ≫ f).stalkMap x :=
    (Scheme.Hom.stalkMap_congr_hom (rX ≫ f) (f₀ ≫ rY) hfac.symm x).symm
  simpa only [κ, Scheme.Hom.stalkMap_comp, Category.assoc] using hh'

/-- Passing to reductions does not change the local rings: if a morphism induces an isomorphism
of local rings at a point, so does the induced morphism of reductions at the corresponding
point. -/
private theorem isIso_stalkMap_reductionMap {T X : Scheme.{u}} (f : T ⟶ X)
    (x : T) (h : IsIso (f.stalkMap x)) :
    IsIso ((Scheme.reductionMap f).stalkMap ((Scheme.reductionHomeo T).symm x)) := by
  let rT : T.reduction ⟶ T := T.reductionι
  let rX : X.reduction ⟶ X := X.reductionι
  let eT : T.reduction ≃ₜ T := Scheme.reductionHomeo T
  let x₀ : T.reduction := eT.symm x
  let f₀ : T.reduction ⟶ X.reduction := Scheme.reductionMap f
  have hfac : f₀ ≫ rX = rT ≫ f := Scheme.reductionMap_comp_reductionι f
  have hx₀ : rT x₀ = x := eT.apply_symm_apply x
  have hpoint : rX (f₀ x₀) = f (rT x₀) :=
    congrArg (fun k : T.reduction ⟶ X => k x₀) hfac
  let α := f.stalkMap (rT x₀)
  let β := rX.stalkMap (f₀ x₀)
  let γ := rT.stalkMap x₀
  let δ := f₀.stalkMap x₀
  let κ := X.presheaf.stalkSpecializes (Inseparable.of_eq hpoint.symm).ge
  let β' := κ ≫ β
  have hmaps : β' ≫ δ = α ≫ γ :=
    stalkSpecializes_comp_stalkMap_comp_of_comp_eq hfac x₀ hpoint
  have : IsIso α := by
    show IsIso (f.stalkMap (rT x₀))
    rwa [hx₀]
  have hβ' : Function.Surjective β' := by
    intro z
    obtain ⟨b, hb⟩ : ∃ b, β b = z := rX.stalkMap_surjective (f₀ x₀) z
    have : IsIso κ :=
      inferInstanceAs (IsIso (X.presheaf.stalkCongr (Inseparable.of_eq hpoint.symm)).hom)
    obtain ⟨a, ha⟩ := (ConcreteCategory.bijective_of_isIso κ).2 b
    exact ⟨a, by simp [β', ha, hb]⟩
  have hδ : Function.Bijective δ.hom :=
    bijective_of_square_of_surjective α.hom β'.hom γ.hom δ.hom
      ((ConcreteCategory.isIso_iff_bijective α).mp inferInstance) hβ'
      (rT.stalkMap_surjective x₀) (ker_stalkMap_reductionι_le_nilradical (X := T) x₀)
      fun a => by simpa [CommRingCat.hom_comp, β'] using congrArg (fun k => k.hom a) hmaps
  simpa [δ, f₀, x₀, eT] using (ConcreteCategory.isIso_iff_bijective δ).2 hδ

/-- If a composition of maps of rings is an isomorphism and the second map is injective, then
the second map is an isomorphism. -/
private lemma isIso_of_isIso_comp_of_injective
    {A B C : CommRingCat.{u}} (f : A ⟶ B) (g : B ⟶ C)
    (hfg : IsIso (f ≫ g)) (hg : Function.Injective g.hom) : IsIso g :=
  (ConcreteCategory.isIso_iff_bijective g).2
    ⟨hg, Function.Surjective.of_comp (ConcreteCategory.bijective_of_isIso (f ≫ g)).2⟩

/-- Every generic point of the target of a quasi-compact dominant morphism of schemes is the
image of a generic point of the source. -/
theorem exists_mem_genericPoints_eq_of_isDominant {T Z : Scheme.{u}} (q : T ⟶ Z)
    [QuasiCompact q] [IsDominant q] {z : Z} (hz : z ∈ genericPoints Z) :
    ∃ η ∈ genericPoints T, q η = z := by
  obtain ⟨x, hx⟩ := ((isDominant_iff_genericPoints_subset_range q).mp inferInstance) hz
  obtain ⟨η, hη, hηx⟩ := exists_mem_genericPoints_specializes x
  refine ⟨η, hη, ?_⟩
  have hηz : q η ⤳ z := by simpa [hx] using hηx.map q.continuous
  exact (mem_genericPoints_iff_forall_specializes_eq z).1 hz _ hηz

/-- A morphism from an affine scheme which is injective on generic points, and which is an open
immersion on each member of a family of opens, is an open immersion on their union. -/
theorem isOpenImmersion_iSup_ι_comp_of_genericPoints_injOn {Z X : Scheme.{u}} [IsAffine Z]
    (g : Z ⟶ X) {ι : Type v} (U : ι → Z.Opens) (hU : ∀ k, IsOpenImmersion ((U k).ι ≫ g))
    (hinj : Set.InjOn g (genericPoints Z)) : IsOpenImmersion ((⨆ k, U k).ι ≫ g) := by
  let V : Z.Opens := ⨆ k, U k
  let gV : V.toScheme ⟶ X := V.ι ≫ g
  let cover : V.toScheme.OpenCover := Scheme.Opens.iSupOpenCover U
  have hcover : ∀ k, IsOpenImmersion (cover.f k ≫ gV) := fun k => by
    rw [show cover.f k ≫ gV = (U k).ι ≫ g by simp [cover, gV, V, Scheme.Opens.iSupOpenCover]]
    exact hU k
  have hVgeneric : Set.MapsTo V.ι (genericPoints V.toScheme) (genericPoints Z) := by
    intro z hz
    apply (mem_genericPoints_iff_forall_specializes_eq (V.ι z)).2
    intro y hy
    have hyV : y ∈ V := hy.mem_open V.2 z.2
    have hyz : (⟨y, hyV⟩ : V.toScheme) ⤳ z :=
      V.ι.isOpenEmbedding.isInducing.specializes_iff.1 hy
    exact congrArg Subtype.val
      ((mem_genericPoints_iff_forall_specializes_eq z).1 hz _ hyz)
  have : Scheme.IsSeparated V.toScheme :=
    ⟨by simpa [gV, V, Category.assoc] using
      (inferInstance : IsSeparated (V.ι ≫ Limits.terminal.from Z))⟩
  have : IsSeparated gV := IsSeparated.of_comp gV (Limits.terminal.from X)
  exact isOpenImmersion_of_openCover_source_of_separated_of_genericPoints_injOn
    gV cover hcover fun z hz w hw heq => Subtype.ext (hinj (hVgeneric hz) (hVgeneric hw) heq)

/-- A morphism from an affine reduced scheme to a quasi-separated scheme factors as a
quasi-compact dominant morphism onto an affine reduced scheme followed by a morphism locally of
finite type. -/
private lemma exists_isAffine_isReduced_isDominant_factorization {T X : Scheme.{u}} (f : T ⟶ X)
    [IsAffine T] [QuasiSeparatedSpace X] [IsReduced T] :
    ∃ (Z : Scheme.{u}) (q : T ⟶ Z) (g : Z ⟶ X), IsAffine Z ∧ IsReduced Z ∧ QuasiCompact q ∧
      IsDominant q ∧ LocallyOfFiniteType g ∧ q ≫ g = f := by
  obtain ⟨I, hIpre, hInonempty, hIdir, D, tD, p, hp, hcompat, hfp, hDqcqs,
    htransition⟩ := AlgebraicGeometry.exists_isLimit_finitePresentation f
  let : Preorder I := hIpre
  let : Nonempty I := hInonempty
  let : IsDirectedOrder I := hIdir
  let Dsmall : Iᵒᵖ ⥤ Scheme.{u} := D
  let csmall : CategoryTheory.Limits.Cone Dsmall := CategoryTheory.Limits.Cone.mk T p
  have hcsmall : CategoryTheory.Limits.IsLimit csmall := hp
  have : IsAffine csmall.pt := inferInstanceAs (IsAffine T)
  have : ∀ i : Iᵒᵖ, CompactSpace (Dsmall.obj i) := fun i => (hDqcqs i).1
  have : ∀ i : Iᵒᵖ, QuasiSeparatedSpace (Dsmall.obj i) := fun i => (hDqcqs i).2
  have : ∀ {i j : Iᵒᵖ} (g : i ⟶ j), IsAffineHom (Dsmall.map g) := htransition
  obtain ⟨iSmall, hiSmallAffine⟩ := Scheme.exists_isAffine_of_isLimit Dsmall csmall hcsmall
  let i : I := iSmall.unop
  let Y : Scheme := D.obj (Opposite.op i)
  let q : T ⟶ Y := p.app (Opposite.op i)
  let g : Y ⟶ X := tD.app (Opposite.op i)
  have hqg : q ≫ g = f := by
    simpa [q, g] using congrArg (fun α => α.app (Opposite.op i)) hcompat
  have : IsAffine Y := by simpa [Y, Dsmall] using hiSmallAffine
  have : LocallyOfFinitePresentation g := (hfp (Opposite.op i)).1
  exact ⟨q.image, q.toImage, q.imageι ≫ g, isAffine_of_isAffineHom q.imageι, inferInstance,
    inferInstance, inferInstance, inferInstance, by rw [← Category.assoc, q.toImage_imageι, hqg]⟩

/-- Let `q : T ⟶ Z` be quasi-compact and dominant with `Z` reduced. If `q ≫ g` carries generic
points injectively to generic points and induces an isomorphism of local rings at `t`, then `g`
induces an isomorphism of local rings at `q t`. -/
private lemma isIso_stalkMap_of_isIso_stalkMap_comp {T Z X : Scheme.{u}} (q : T ⟶ Z)
    (g : Z ⟶ X) [QuasiCompact q] [IsDominant q] [IsReduced Z]
    (hgeneric : Set.MapsTo (q ≫ g) (genericPoints T) (genericPoints X))
    (hinj : Set.InjOn (q ≫ g) (genericPoints T)) (t : T)
    (hstalk : IsIso ((q ≫ g).stalkMap t)) : IsIso (g.stalkMap (q t)) := by
  have hcomp : IsIso (g.stalkMap (q t) ≫ q.stalkMap t) := by
    rwa [← Scheme.Hom.stalkMap_comp]
  have hker := ker_stalkMap_le_nilradical_of_genericPoints q t fun θ hθ hθt => by
    obtain ⟨η₀, hη₀, hη₀θ⟩ := exists_mem_genericPoints_eq_of_isDominant q hθ
    have hθf : (q ≫ g) η₀ ⤳ (q ≫ g) t := by
      simpa only [Scheme.Hom.comp_apply, hη₀θ] using hθt.map g.continuous
    obtain ⟨η, hη, hηt, hηf⟩ :=
      exists_mem_genericPoints_specializes_of_isIso_stalkMap (q ≫ g) t hstalk (hgeneric hη₀) hθf
    obtain rfl : η = η₀ := hinj hη hη₀ hηf
    exact ⟨η, hηt, hη₀θ⟩
  have : IsIso (q.stalkMap t) := isIso_of_isIso_comp_of_injective _ _ hcomp
    ((RingHom.injective_iff_ker_eq_bot _).2 (by simpa using hker))
  exact IsIso.of_isIso_comp_right (g.stalkMap (q t)) (q.stalkMap t)

/-- The reduced case after factoring through a dominant morphism onto an affine scheme: the
images of the points lie in an affine open of the target. -/
private theorem exists_isAffineOpen_containing_image_of_isDominant_comp {T Z X : Scheme.{u}}
    (q : T ⟶ Z) (g : Z ⟶ X) [IsAffine Z] [IsReduced Z] [IsReduced X] [QuasiCompact q]
    [IsDominant q] [LocallyOfFiniteType g] (hX : (irreducibleComponents X).Finite)
    (hgeneric : Set.MapsTo (q ≫ g) (genericPoints T) (genericPoints X))
    (hinj : Set.InjOn (q ≫ g) (genericPoints T))
    {ι : Type v} [Finite ι] (t : ι → T)
    (hstalk : ∀ i, IsIso ((q ≫ g).stalkMap (t i))) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ i, (q ≫ g) (t i) ∈ U := by
  have hgInj : Set.InjOn g (genericPoints Z) := by
    intro z₁ hz₁ z₂ hz₂ heq
    obtain ⟨η₁, hη₁, rfl⟩ := exists_mem_genericPoints_eq_of_isDominant q hz₁
    obtain ⟨η₂, hη₂, rfl⟩ := exists_mem_genericPoints_eq_of_isDominant q hz₂
    exact congrArg q (hinj hη₁ hη₂ heq)
  choose U hUt hUimm using fun k => exists_isOpenImmersion_res_of_isIso_stalkMap g (q (t k)) hX
    (isIso_stalkMap_of_isIso_stalkMap_comp q g hgeneric hinj (t k) (hstalk k))
  let V : Z.Opens := ⨆ k, U k
  have : IsOpenImmersion (V.ι ≫ g) :=
    isOpenImmersion_iSup_ι_comp_of_genericPoints_injOn g U hUimm hgInj
  let s : ι → V.toScheme := fun k => ⟨q (t k), (Opens.mem_iSup).2 ⟨k, hUt k⟩⟩
  obtain ⟨W, hW, hEW⟩ :=
    Stacks.AmpleCluster.exists_affineOpen_containing_finite_of_immersion_affine V.ι
      (Set.finite_range s)
  refine ⟨(V.ι ≫ g) ''ᵁ W, hW.image_of_isOpenImmersion (V.ι ≫ g), fun k => ?_⟩
  show (V.ι ≫ g) (s k) ∈ (V.ι ≫ g) ''ᵁ W
  exact Set.mem_image_of_mem (V.ι ≫ g) (hEW ⟨k, rfl⟩)

/-- **[Stacks, Tag 09NI] for reduced schemes.** A finite family of points on a reduced affine
scheme whose local rings agree with those of a reduced quasi-separated target with finitely many
generic points has its image contained in an affine open of the target, provided the generic
points map injectively to generic points. -/
private theorem exists_isAffineOpen_containing_image_of_isReduced
    {T X : Scheme.{u}} (f : T ⟶ X) [IsAffine T] [QuasiSeparatedSpace X]
    [IsReduced T] [IsReduced X]
    (hX : (genericPoints X).Finite)
    (hgeneric : Set.MapsTo f (genericPoints T) (genericPoints X))
    (hinj : Set.InjOn f (genericPoints T))
    {ι : Type v} [Finite ι] (t : ι → T)
    (hstalk : ∀ i, IsIso (f.stalkMap (t i))) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ i, f (t i) ∈ U := by
  obtain ⟨Z, q, g, _, _, _, _, _, rfl⟩ := exists_isAffine_isReduced_isDominant_factorization f
  exact exists_isAffineOpen_containing_image_of_isDominant_comp q g
    (finite_irreducibleComponents_of_finite_genericPoints hX) hgeneric hinj t hstalk

/-- The image in a scheme of an affine open of its reduction is an affine open. -/
theorem isAffineOpen_image_reductionHomeo {X : Scheme.{u}} {U₀ : X.reduction.Opens}
    (hU₀ : IsAffineOpen U₀) :
    IsAffineOpen (⟨Scheme.reductionHomeo X '' (U₀ : Set X.reduction),
      (Scheme.reductionHomeo X).isOpenMap _ U₀.2⟩ : X.Opens) := by
  let rX : X.reduction ⟶ X := X.reductionι
  let eX : X.reduction ≃ₜ X := Scheme.reductionHomeo X
  let U : X.Opens := ⟨eX '' (U₀ : Set X.reduction), eX.isOpenMap _ U₀.2⟩
  have hpre : rX ⁻¹ᵁ U = U₀ := by
    ext z
    show rX z ∈ eX '' (U₀ : Set X.reduction) ↔ z ∈ U₀
    refine ⟨?_, fun hz => ⟨z, hz, rfl⟩⟩
    rintro ⟨w, hw, hzw⟩
    simpa [eX.injective (show eX z = eX w from hzw.symm)] using hw
  have : IsAffine ((rX ⁻¹ᵁ U).toScheme) := by rwa [hpre]
  have hsurj : Function.Surjective (rX ∣_ U).base := by
    intro y
    have hry : rX (eX.symm y.1) = y.1 := eX.apply_symm_apply y.1
    have hy : rX (eX.symm y.1) ∈ U := hry.symm ▸ y.2
    exact ⟨⟨eX.symm y.1, hy⟩, Subtype.ext ((morphismRestrict_base_coe rX U _).trans hry)⟩
  have : Surjective (rX ∣_ U) := ⟨hsurj⟩
  exact Stacks.AffineFromUniversallyClosed.isAffine_of_surjective_universallyClosed (rX ∣_ U)

/-- **[Stacks, Tag 09NI].** Let `f : T ⟶ X` be a morphism of schemes with `T` affine and `X`
quasi-separated with finitely many generic points. If `f` carries the generic points of the
irreducible components of `T` into those of `X` and does so injectively, and if the canonical
map of local rings at each member of a finite family of points of `T` is an isomorphism, then
the images of that family lie in a common affine open of `X`. -/
@[stacks 09NI]
public theorem exists_isAffineOpen_containing_image_of_genericPoints_injOn
    {T X : Scheme.{u}} (f : T ⟶ X) [IsAffine T] [QuasiSeparatedSpace X]
    (hX : (genericPoints X).Finite)
    (hgeneric : Set.MapsTo f (genericPoints T) (genericPoints X))
    (hinj : Set.InjOn f (genericPoints T))
    {ι : Type v} [Finite ι] (t : ι → T)
    (hstalk : ∀ i, IsIso (f.stalkMap (t i))) :
    ∃ U : X.Opens, IsAffineOpen U ∧ ∀ i, f (t i) ∈ U := by
  let rT : T.reduction ⟶ T := T.reductionι
  let rX : X.reduction ⟶ X := X.reductionι
  let eT : T.reduction ≃ₜ T := Scheme.reductionHomeo T
  let eX : X.reduction ≃ₜ X := Scheme.reductionHomeo X
  let f₀ : T.reduction ⟶ X.reduction := Scheme.reductionMap f
  let t₀ : ι → T.reduction := fun i => eT.symm (t i)
  have : IsAffine T.reduction := isAffine_of_isAffineHom rT
  have : QuasiSeparatedSpace X.reduction :=
    (quasiSeparatedSpace_congr eX).mpr inferInstance
  have hX₀ : (genericPoints X.reduction).Finite :=
    (hX.preimage eX.injective.injOn).subset fun y hy => (eX.mem_genericPoints_iff y).mpr hy
  have hpoint : ∀ z : T.reduction, rX (f₀ z) = f (rT z) := Scheme.reductionMap_apply f
  have hgeneric₀ : Set.MapsTo f₀ (genericPoints T.reduction) (genericPoints X.reduction) := by
    intro z hz
    refine (eX.mem_genericPoints_iff (f₀ z)).mp ?_
    rw [show eX (f₀ z) = rX (f₀ z) from rfl, hpoint]
    exact hgeneric ((eT.mem_genericPoints_iff z).mpr hz)
  have hinj₀ : Set.InjOn f₀ (genericPoints T.reduction) := by
    intro z hz w hw hzw
    exact eT.injective (hinj ((eT.mem_genericPoints_iff z).mpr hz)
      ((eT.mem_genericPoints_iff w).mpr hw)
      ((hpoint z).symm.trans ((congrArg rX hzw).trans (hpoint w))))
  obtain ⟨U₀, hU₀, hpoints₀⟩ := exists_isAffineOpen_containing_image_of_isReduced f₀ hX₀
    hgeneric₀ hinj₀ t₀ fun i => isIso_stalkMap_reductionMap f (t i) (hstalk i)
  refine ⟨_, isAffineOpen_image_reductionHomeo hU₀, fun i => ?_⟩
  have hpointi : eX (f₀ (t₀ i)) = f (t i) :=
    (hpoint _).trans (congrArg f (eT.apply_symm_apply (t i)))
  rw [← hpointi]
  exact Set.mem_image_of_mem eX (hpoints₀ i)

end AlgebraicGeometry

end
