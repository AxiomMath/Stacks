module

public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocusFreeAlong
public import StacksFrontier.AlgebraicGeometry.Morphisms.DescentLocusClosedness
public import StacksFrontier.AlgebraicGeometry.Cohomology.MinimalComplexFunctoriality.TrivialNearFibre
public import StacksFrontier.AlgebraicGeometry.Etale.NeighborhoodStalkFiber
import StacksCore.Tactic.EgaSgaAttribute

/-!
# The descent locus of a module near a point is the intersection of the loci of its restrictions

Let `f : X ⟶ S` and the composites `i k ≫ f : Y k ⟶ S` (`k` in a finite type) be flat, proper and
of finite presentation with `𝒪_T ≅ p_*𝒪` after every base change, let `ℒ` be an invertible
`𝒪_X`-module and `ℒ_k = (i k)^*ℒ`, and let `Z` and the `Z_k` be descent loci
(`AlgebraicGeometry.IsDescentLocus`, [Stacks, Tag 0BDP]) of `ℒ` over `f` and of `ℒ_k` over
`i k ≫ f`. A module descending from the base pulls back to modules descending from the base, so
`Z ⊆ ⋂ Z_k`. [Stacks, Tag 0BF2] says that near a point `s ∈ Z` at which
`H¹(X_s, 𝒪) ⟶ ⊕_k H¹(Y_{k,s}, 𝒪)` is injective the two agree: `Z ∩ U = (⋂ Z_k) ∩ U`, as
subschemes, for an open neighbourhood `U` of `s`.

The proof is the source's. The scheme theoretic intersection `W` of the `Z_k`
(`AlgebraicGeometry.exists_isImmersion_factorsThrough_iff_forall`) is a base along which every
`ℒ_k` descends; over an open neighbourhood `V ⊆ W` of the point above `s` the descended modules are
trivial, so every `ℒ_k` is trivial over `Y_k ×_S V`, and the case of trivial faces
(`SheafOfModules.exists_isTrivial_modulePullback_fst_ι_of_injective_H1_of_isPullback`) trivializes
`ℒ` over `X ×_S U'` for an open `U' ⊆ V` containing that point. As `W ⟶ S` is an embedding,
`U'` is cut out of `W` by an open `U` of `S`, and a morphism `T ⟶ U` factoring through every
`Z_k` factors through `U'`, along which `ℒ` descends.

## Main results

* `AlgebraicGeometry.exists_isImmersion_factorsThrough_iff_forall`: finitely many immersions into
  `S` have a scheme theoretic intersection, an immersion through which a morphism factors exactly
  when it factors through each of them.
* `AlgebraicGeometry.exists_comp_eq_fromSpecResidueField_of_mem_range`: the residue field point of
  a point in the image of a preimmersion factors through it.
* `AlgebraicGeometry.DescendsFromBase.comp_left`: a module descending from the base along `g`
  pulls back, along any `a : Y ⟶ X`, to a module descending from the base along `g`.
* `AlgebraicGeometry.IsDescentLocus.exists_factorsThrough_iff_forall_of_injective_H1`:
  [Stacks, Tag 0BF2].

## Implementation notes

"`Z ∩ U = (⋂ Z_k) ∩ U` as subschemes of `U`" is stated through the functors of points: a morphism
`g : T ⟶ S` with image in `U` factors through `Z` exactly when it factors through every `Z_k`.
Both sides are subschemes of `U`, that is monomorphisms into it, and two subschemes are equal
exactly when the same morphisms factor through them; the right-hand side is the universal property
of the scheme theoretic intersection.

The loci are arbitrary descent loci, as in Tag 0BF0
(`IsDescentLocus.isClosedImmersion_hom_of_geometricallyIntegral`): any two are isomorphic over
`S` (`IsDescentLocus.isoOfIsDescentLocus`), so this is the statement for the loci of Tag 0BDP,
and no existence statement is used.

## References

* [Stacks Project, Tag 0BF2](https://stacks.math.columbia.edu/tag/0BF2)
* [Stacks Project, Tag 0BF1](https://stacks.math.columbia.edu/tag/0BF1)
* [Stacks Project, Tag 0BDP](https://stacks.math.columbia.edu/tag/0BDP)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace
open RingedSpaceModuleAdjunction
open AlgebraicGeometry.SheafOfModules (IsTrivial IsInvertible)
open Stacks.Cohomology.GlobalKunneth (sectionsOverBase baseRing sectionsPullbackMap)
open AlgebraicGeometry.BottomRankStratum (comp_toLRSHom_toShHom)

universe u

namespace AlgebraicGeometry

/-- **Finite intersections of immersions.** Finitely many immersions `Z k ⟶ S` have a scheme
theoretic intersection: an immersion `W ⟶ S` through which a morphism `g : T ⟶ S` factors exactly
when `g` factors through every `Z k`. It is the iterated fibre product over `S`. -/
@[ega "IV 17.13.11"]
theorem exists_isImmersion_factorsThrough_iff_forall {S : Scheme.{u}} {ι : Type*} [Finite ι]
    (Z : ι → Over S) (hZ : ∀ k, IsImmersion (Z k).hom) :
    ∃ W : Over S, IsImmersion W.hom ∧ ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (∃ h : T ⟶ W.left, h ≫ W.hom = g) ↔ ∀ k, ∃ h : T ⟶ (Z k).left, h ≫ (Z k).hom = g := by
  classical
  have := Fintype.ofFinite ι
  suffices H : ∀ A : Finset ι, ∃ W : Over S, IsImmersion W.hom ∧ ∀ {T : Scheme.{u}} (g : T ⟶ S),
      (∃ h : T ⟶ W.left, h ≫ W.hom = g) ↔ ∀ k ∈ A, ∃ h : T ⟶ (Z k).left, h ≫ (Z k).hom = g by
    obtain ⟨W, hW, hg⟩ := H Finset.univ
    exact ⟨W, hW, fun g => (hg g).trans
      ⟨fun H k => H k (Finset.mem_univ k), fun H k _ => H k⟩⟩
  intro A
  induction A using Finset.induction_on with
  | empty =>
    exact ⟨Over.mk (𝟙 S), inferInstanceAs (IsImmersion (𝟙 S)), fun g =>
      ⟨fun _ k hk => absurd hk (Finset.notMem_empty k), fun _ => ⟨g, Category.comp_id g⟩⟩⟩
  | insert k₀ A _ ih =>
    obtain ⟨W, _, hg⟩ := ih
    have := hZ k₀
    refine ⟨Over.mk (pullback.fst W.hom (Z k₀).hom ≫ W.hom),
      inferInstanceAs (IsImmersion (pullback.fst W.hom (Z k₀).hom ≫ W.hom)), fun g => ⟨?_, ?_⟩⟩
    · rintro ⟨h, rfl⟩ k hk
      rcases Finset.mem_insert.1 hk with rfl | hk
      · exact ⟨h ≫ pullback.snd _ _, by
          simp only [Over.mk_hom, Category.assoc, pullback.condition]⟩
      · obtain ⟨a, ha⟩ := (hg W.hom).1 ⟨𝟙 _, Category.id_comp _⟩ k hk
        exact ⟨h ≫ pullback.fst _ _ ≫ a, by simp only [Over.mk_hom, Category.assoc, ha]⟩
    · intro H
      obtain ⟨a, ha⟩ := (hg g).2 fun k hk => H k (Finset.mem_insert_of_mem hk)
      obtain ⟨b, hb⟩ := H k₀ (Finset.mem_insert_self k₀ A)
      exact ⟨pullback.lift a b (by rw [ha, hb]), by
        simp only [Over.mk_hom, pullback.lift_fst_assoc, ha]⟩

/-- **The residue field point of a point of a preimmersion factors through it.** If `s` lies in
the image of a preimmersion `j : Z ⟶ S`, then `Spec κ(s) ⟶ S` factors through `j`: at a point
`z` over `s` the map `κ(s) ⟶ κ(z)` is an isomorphism, `j` being surjective on stalks. -/
theorem exists_comp_eq_fromSpecResidueField_of_mem_range {Z S : Scheme.{u}} (j : Z ⟶ S)
    [IsPreimmersion j] (s : S) (hs : s ∈ Set.range j) :
    ∃ t : Spec (S.residueField s) ⟶ Z, t ≫ j = S.fromSpecResidueField s := by
  obtain ⟨z, rfl⟩ := hs
  have := j.isIso_residueFieldMap_of_surjectiveOnStalks z
  refine ⟨Spec.map (inv (j.residueFieldMap z)) ≫ Z.fromSpecResidueField z, ?_⟩
  rw [Category.assoc, ← Scheme.Hom.SpecMap_residueFieldMap_fromSpecResidueField,
    ← Spec.map_comp_assoc, IsIso.hom_inv_id, Spec.map_id, Category.id_comp]

/-- A morphism `t : Spec κ(s) ⟶ Z` over `Spec κ(s) ⟶ S` along `j : Z ⟶ S` sends every point to
a point over `s`. -/
private theorem apply_of_comp_eq_fromSpecResidueField {Z S : Scheme.{u}} {j : Z ⟶ S} {s : S}
    {t : Spec (S.residueField s) ⟶ Z} (ht : t ≫ j = S.fromSpecResidueField s)
    (x : Spec (S.residueField s)) : j (t x) = s := by
  rw [← Scheme.Hom.comp_apply, ht]
  exact Scheme.fromSpecResidueField_apply s x

/-- **Pullbacks along two factorizations agree.** If `a ≫ b = c ≫ d`, then `a^* b^* ℳ` and
`c^* d^* ℳ` are isomorphic. -/
private noncomputable def modulePullbackObjIsoOfCompEq {A B C D : Scheme.{u}} {a : A ⟶ B}
    {b : B ⟶ D} {c : A ⟶ C} {d : C ⟶ D} (h : a ≫ b = c ≫ d)
    (M : SheafOfModules.{u} (structureSheafRing D.toRingedSpace)) :
    (modulePullback a.toLRSHom.toShHom).obj ((modulePullback b.toLRSHom.toShHom).obj M) ≅
      (modulePullback c.toLRSHom.toShHom).obj ((modulePullback d.toLRSHom.toShHom).obj M) :=
  ((modulePullbackComp a.toLRSHom.toShHom b.toLRSHom.toShHom).app M).symm ≪≫
    (modulePullbackCongr (show a.toLRSHom.toShHom ≫ b.toLRSHom.toShHom =
        c.toLRSHom.toShHom ≫ d.toLRSHom.toShHom by
      rw [← comp_toLRSHom_toShHom, h, comp_toLRSHom_toShHom])).app M ≪≫
    (modulePullbackComp c.toLRSHom.toShHom d.toLRSHom.toShHom).app M

variable {X S : Scheme.{u}} (f : X ⟶ S)
  (E : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))

/-- The base change of `a : Y ⟶ X` along `g` commutes with the projections to `T`. -/
private theorem pullback_map_comp_snd {Y T : Scheme.{u}} (g : T ⟶ S) (a : Y ⟶ X) :
    pullback.map (a ≫ f) g f g a (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.snd f g =
      pullback.snd (a ≫ f) g := by
  simp only [pullback.map, pullback.lift_snd, Category.comp_id]

/-- The base change of `a : Y ⟶ X` along `g` commutes with the projections to `X` and `Y`. -/
private theorem pullback_map_comp_fst {Y T : Scheme.{u}} (g : T ⟶ S) (a : Y ⟶ X) :
    pullback.map (a ≫ f) g f g a (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ pullback.fst f g =
      pullback.fst (a ≫ f) g ≫ a := by
  simp only [pullback.map, pullback.lift_fst]

/-- **Base change of a fibre square.** If `t : T ⟶ V` lies over `e : T ⟶ S`, then `X ×_S T` is
the pullback of `X ×_S V ⟶ V` along `t`, through the lift of `t`. -/
private theorem isPullback_lift_snd_of_comp_eq {V T : Scheme.{u}} {v : V ⟶ S} {e : T ⟶ S}
    {t : T ⟶ V} (ht : t ≫ v = e) :
    IsPullback (pullback.lift (pullback.fst f e) (pullback.snd f e ≫ t)
      (by rw [pullback.condition, Category.assoc, ht]))
      (pullback.snd f e) (pullback.snd f v) t := by
  refine IsPullback.of_right ?_ (pullback.lift_snd _ _ _) (IsPullback.of_hasPullback f v)
  rw [pullback.lift_fst, ht]
  exact IsPullback.of_hasPullback f e

/-- **Finitely many descended modules are simultaneously free near a point.** If each `ℰ_k`
descends along `w : W ⟶ S` for `g k`, every point of `W` has an open neighbourhood `V` along which
every `ℰ_k` is free, of some rank. -/
private theorem DescendsFromBase.exists_opens_forall_isFreeAlong {ι : Type*} [Finite ι]
    {Y : ι → Scheme.{u}} (g : ∀ k, Y k ⟶ S)
    (M : ∀ k, SheafOfModules.{u} (structureSheafRing (Y k).toRingedSpace)) {W : Scheme.{u}}
    {w : W ⟶ S} (h : ∀ k, DescendsFromBase (g k) (M k) w) (w₀ : W) :
    ∃ (V : W.Opens) (n : ι → ℕ), w₀ ∈ V ∧ ∀ k, IsFreeAlong (g k) (M k) (V.ι ≫ w) (n k) := by
  choose Vk hVk n hn using fun k => (h k).exists_isFreeAlong (g k) (M k) w₀
  let V : W.Opens := ⟨⋂ k, (Vk k : Set W), isOpen_iInter_of_finite fun k => (Vk k).2⟩
  refine ⟨V, n, Set.mem_iInter.2 hVk, fun k => ?_⟩
  have := (hn k).comp (g k) (M k) (W.homOfLE (show V ≤ Vk k from Set.iInter_subset _ k))
  rwa [← Category.assoc, Scheme.homOfLE_ι] at this

/-- **An invertible module free along a base is trivial there.** If an invertible `ℰ` is free
along `g : T ⟶ S` and `f x = g y`, then the pullback of `ℰ` to `X ×_S T` is trivial. -/
private theorem IsFreeAlong.isTrivial_modulePullback_fst {T : Scheme.{u}} {g : T ⟶ S} {n : ℕ}
    [IsInvertible X.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) E]
    (h : IsFreeAlong f E g n) {x : X} {y : T} (hxy : f x = g y) :
    IsTrivial (pullback f g).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) (pullback f g).IsSheaf)
      ((modulePullback (pullback.fst f g).toLRSHom.toShHom).obj E) := by
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := g) x y hxy
  have : Nonempty ↥(pullback f g : Scheme.{u}) := ⟨z⟩
  have := modulePullback_isInvertible_scheme (pullback.fst f g) E
  exact nonempty_iso_unit_of_iso_free _ h.some

/-- **Descent along an open of an immersion is cut out by an open of the base.** If `w : W ⟶ S`
is an immersion and `ℰ` descends along `j ≫ w` for an open immersion `j : U ⟶ W`, then
`j(U) = w⁻¹(U₀)` for an open `U₀` of `S` such that `ℰ` descends along every `h ≫ w` with image in
`U₀`. -/
private theorem DescendsFromBase.exists_opens_forall_of_isOpenImmersion {W U : Scheme.{u}}
    {w : W ⟶ S} [IsImmersion w] {j : U ⟶ W} [IsOpenImmersion j]
    (hD : DescendsFromBase f E (j ≫ w)) :
    ∃ U₀ : S.Opens, w ⁻¹' U₀ = Set.range j ∧ ∀ {T : Scheme.{u}} (h : T ⟶ W),
      Set.range (h ≫ w) ⊆ U₀ → DescendsFromBase f E (h ≫ w) := by
  obtain ⟨U₀, hU₀, hpre⟩ := w.isEmbedding.isInducing.isOpen_iff.1 j.isOpenEmbedding.isOpen_range
  refine ⟨⟨U₀, hU₀⟩, hpre, fun h hh => ?_⟩
  have hr : Set.range h ⊆ Set.range j := by
    rintro _ ⟨x, rfl⟩
    rw [← hpre]
    exact hh ⟨x, (Scheme.Hom.comp_apply h w x).symm⟩
  rw [← IsOpenImmersion.lift_fac j h hr, Category.assoc]
  exact hD.precomp _

/-- **Descent from the base is inherited by pullbacks.** If `ℰ` descends along `g : T ⟶ S` for
`f`, with descended module `N`, then for every `a : Y ⟶ X` the module `a^*ℰ` descends along `g`
for `a ≫ f`, with the same descended module: the base change `Y ×_S T ⟶ X ×_S T` of `a`
identifies the two pullbacks. -/
theorem DescendsFromBase.comp_left {T : Scheme.{u}} {g : T ⟶ S}
    (h : DescendsFromBase f E g) {Y : Scheme.{u}} (a : Y ⟶ X) :
    DescendsFromBase (a ≫ f) ((modulePullback a.toLRSHom.toShHom).obj E) g := by
  obtain ⟨N, hN, ⟨e⟩⟩ := h
  let m : pullback (a ≫ f) g ⟶ pullback f g :=
    pullback.map (a ≫ f) g f g a (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hm₁ : m ≫ pullback.snd f g = pullback.snd (a ≫ f) g := pullback_map_comp_snd f g a
  have hm₂ : m ≫ pullback.fst f g = pullback.fst (a ≫ f) g ≫ a := pullback_map_comp_fst f g a
  exact ⟨N, hN, ⟨(modulePullbackCongr (show (pullback.snd (a ≫ f) g).toLRSHom.toShHom =
        m.toLRSHom.toShHom ≫ (pullback.snd f g).toLRSHom.toShHom by
      rw [← comp_toLRSHom_toShHom, hm₁])).app N ≪≫
    (modulePullbackComp m.toLRSHom.toShHom (pullback.snd f g).toLRSHom.toShHom).app N ≪≫
    (modulePullback m.toLRSHom.toShHom).mapIso e ≪≫ modulePullbackObjIsoOfCompEq hm₂ E⟩⟩

attribute [local instance 10000] HasDerivedCategory.standard

/-- **The case of trivial faces over a base through which `Spec κ(s) ⟶ S` factors.** In the
situation of Tag 0BF2, let `t : Spec κ(s) ⟶ V` lie over `Spec κ(s) ⟶ S` along `v : V ⟶ S`, and
let `ℳ` be an invertible module on `X ×_S V` whose pullbacks to every `Y k ×_S V` and to the fibre
`X_s` are trivial. Then `ℳ` is trivial over `X ×_S U'` for an open `U'` of `V` containing the
image of `t`. -/
private theorem exists_opens_isTrivial_of_injective_H1_of_comp_eq
    [Flat f] [IsProper f] (hfp : FinitePresentation f) (s : S)
    (hO : IsIso (structureSheafHom (pullback.snd f (S.fromSpecResidueField s)).toLRSHom.toShHom))
    {ι : Type u} [Finite ι] (Y : ι → Scheme.{u}) (i : ∀ k, Y k ⟶ X)
    (hflat : ∀ k, Flat (i k ≫ f)) (hprop : ∀ k, IsProper (i k ≫ f))
    (hfpk : ∀ k, FinitePresentation (i k ≫ f))
    (hOk : ∀ k, IsIso (structureSheafHom
      (pullback.snd (i k ≫ f) (S.fromSpecResidueField s)).toLRSHom.toShHom))
    (hinj : ∀ c : (DerivedCategory.homologyFunctor
          (ModuleCat.{u} (baseRing (Spec (S.residueField s)).toRingedSpace)) 1).obj
        ((sectionsOverBase (pullback.snd f (S.fromSpecResidueField s)).toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (SheafOfModules.unit (structureSheafRing
              (pullback f (S.fromSpecResidueField s)).toRingedSpace))))),
      (∀ k, ((DerivedCategory.homologyFunctor _ 1).map
          (sectionsPullbackMap (pullback.snd f (S.fromSpecResidueField s)).toLRSHom.toShHom
            (pullback.map (i k ≫ f) (S.fromSpecResidueField s) f (S.fromSpecResidueField s)
              (i k) (𝟙 _) (𝟙 _) (by simp) (by simp)).toLRSHom.toShHom
            (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
              (SheafOfModules.unit (structureSheafRing
                (pullback f (S.fromSpecResidueField s)).toRingedSpace)))))).hom c = 0) →
        c = 0)
    {V : Scheme.{u}} (v : V ⟶ S) (t : Spec (S.residueField s) ⟶ V)
    (ht : t ≫ v = S.fromSpecResidueField s)
    (M : SheafOfModules.{u} (structureSheafRing (pullback f v).toRingedSpace))
    [IsInvertible (pullback f v).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) (pullback f v).IsSheaf) M]
    (htriv : ∀ k, IsTrivial (pullback (i k ≫ f) v).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback (i k ≫ f) v).IsSheaf)
      ((modulePullback (pullback.map (i k ≫ f) v f v (i k) (𝟙 _) (𝟙 _) (by simp)
        (by simp)).toLRSHom.toShHom).obj M))
    (hFtriv : IsTrivial (pullback f (S.fromSpecResidueField s)).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback f (S.fromSpecResidueField s)).IsSheaf)
      ((modulePullback (pullback.lift (pullback.fst f (S.fromSpecResidueField s))
        (pullback.snd f (S.fromSpecResidueField s) ≫ t)
        (by rw [pullback.condition, Category.assoc, ht])).toLRSHom.toShHom).obj M)) :
    ∃ U' : V.Opens, Set.range t ⊆ U' ∧
      IsTrivial (pullback (pullback.snd f v) U'.ι).presheaf
        (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
          (pullback (pullback.snd f v) U'.ι).IsSheaf)
        ((modulePullback (pullback.fst (pullback.snd f v) U'.ι).toLRSHom.toShHom).obj M) := by
  classical
  let e := S.fromSpecResidueField s
  obtain ⟨_, _, _⟩ := hfp
  let p := pullback.snd f v
  have hpfp : FinitePresentation p := ⟨inferInstance, inferInstance, inferInstance⟩
  let i' : ∀ k, pullback (i k ≫ f) v ⟶ pullback f v := fun k =>
    pullback.map (i k ≫ f) v f v (i k) (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hi'p : ∀ k, i' k ≫ p = pullback.snd (i k ≫ f) v := (pullback_map_comp_snd f v <| i ·)
  have hbase : ∀ k, Flat (i' k ≫ p) ∧ IsProper (i' k ≫ p) ∧ FinitePresentation (i' k ≫ p) := by
    intro k
    obtain ⟨_, _, _⟩ := hfpk k
    have := hflat k
    have := hprop k
    rw [hi'p]
    exact ⟨inferInstance, inferInstance, inferInstance, inferInstance, inferInstance⟩
  let tF : pullback f e ⟶ pullback f v := pullback.lift (pullback.fst f e)
    (pullback.snd f e ≫ t) (by rw [pullback.condition, Category.assoc, ht])
  let isk : ∀ k, pullback (i k ≫ f) e ⟶ pullback f e := fun k =>
    pullback.map (i k ≫ f) e f e (i k) (𝟙 _) (𝟙 _) (by simp) (by simp)
  have hisk : ∀ k, isk k ≫ pullback.snd f e = pullback.snd (i k ≫ f) e :=
    (pullback_map_comp_snd f e <| i ·)
  let tX : ∀ k, pullback (i k ≫ f) e ⟶ pullback (i k ≫ f) v := fun k =>
    pullback.lift (pullback.fst (i k ≫ f) e) (pullback.snd (i k ≫ f) e ≫ t)
      (by rw [pullback.condition, Category.assoc, ht])
  have hX : ∀ k, IsPullback (tX k) (isk k ≫ pullback.snd f e) (i' k ≫ p) t := fun k => by
    rw [hi'p, hisk]
    exact isPullback_lift_snd_of_comp_eq (i k ≫ f) ht
  have hXF : ∀ k, tX k ≫ i' k = isk k ≫ tF := by
    intro k
    apply pullback.hom_ext
    · simp only [tX, i', isk, tF, pullback.map, Category.assoc, pullback.lift_fst,
        pullback.lift_fst_assoc]
    · simp only [tX, i', isk, tF, pullback.map, Category.assoc, pullback.lift_snd,
        pullback.lift_snd_assoc, Category.comp_id]
  have hXO : ∀ k, IsIso (structureSheafHom (isk k ≫ pullback.snd f e).toLRSHom.toShHom) := by
    intro k
    rw [hisk]
    exact hOk k
  exact SheafOfModules.exists_isTrivial_modulePullback_fst_ι_of_injective_H1_of_isPullback p hpfp
    (fun k => pullback (i k ≫ f) v) i' (fun k => (hbase k).1) (fun k => (hbase k).2.1)
    (fun k => (hbase k).2.2) M htriv (K := S.residueField s) t tF (pullback.snd f e)
    (isPullback_lift_snd_of_comp_eq f ht) hO hFtriv (fun k => pullback (i k ≫ f) e) isk tX hX
    hXF hXO hinj

/-- **Descent near the fibre, over a base through which `Spec κ(s) ⟶ S` factors.** In the
situation of Tag 0BF2, let `t : Spec κ(s) ⟶ V` lie over `Spec κ(s) ⟶ S` along `v : V ⟶ S`, let
`ℒ` descend along `Spec κ(s) ⟶ S`, and let every `ℒ_k` be trivial over `Y k ×_S V`. Then `ℒ`
descends along an open `U'` of `V` containing the image of `t`. -/
private theorem exists_opens_descendsFromBase_of_isTrivial_of_injective_H1
    [Flat f] [IsProper f] (hfp : FinitePresentation f) (s : S)
    (hO : IsIso (structureSheafHom (pullback.snd f (S.fromSpecResidueField s)).toLRSHom.toShHom))
    {ι : Type u} [Finite ι] (Y : ι → Scheme.{u}) (i : ∀ k, Y k ⟶ X)
    (hflat : ∀ k, Flat (i k ≫ f)) (hprop : ∀ k, IsProper (i k ≫ f))
    (hfpk : ∀ k, FinitePresentation (i k ≫ f))
    (hOk : ∀ k, IsIso (structureSheafHom
      (pullback.snd (i k ≫ f) (S.fromSpecResidueField s)).toLRSHom.toShHom))
    (hinj : ∀ c : (DerivedCategory.homologyFunctor
          (ModuleCat.{u} (baseRing (Spec (S.residueField s)).toRingedSpace)) 1).obj
        ((sectionsOverBase (pullback.snd f (S.fromSpecResidueField s)).toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (SheafOfModules.unit (structureSheafRing
              (pullback f (S.fromSpecResidueField s)).toRingedSpace))))),
      (∀ k, ((DerivedCategory.homologyFunctor _ 1).map
          (sectionsPullbackMap (pullback.snd f (S.fromSpecResidueField s)).toLRSHom.toShHom
            (pullback.map (i k ≫ f) (S.fromSpecResidueField s) f (S.fromSpecResidueField s)
              (i k) (𝟙 _) (𝟙 _) (by simp) (by simp)).toLRSHom.toShHom
            (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
              (SheafOfModules.unit (structureSheafRing
                (pullback f (S.fromSpecResidueField s)).toRingedSpace)))))).hom c = 0) →
        c = 0)
    (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [hL : IsInvertible X.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) L]
    (hDe : DescendsFromBase f L (S.fromSpecResidueField s))
    {V : Scheme.{u}} (v : V ⟶ S) (t : Spec (S.residueField s) ⟶ V)
    (ht : t ≫ v = S.fromSpecResidueField s)
    (htrivV : ∀ k, IsTrivial (pullback (i k ≫ f) v).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat)
        (pullback (i k ≫ f) v).IsSheaf)
      ((modulePullback (pullback.fst (i k ≫ f) v).toLRSHom.toShHom).obj
        ((modulePullback (i k).toLRSHom.toShHom).obj L))) :
    ∃ U' : V.Opens, Set.range t ⊆ U' ∧ DescendsFromBase f L (U'.ι ≫ v) := by
  let e := S.fromSpecResidueField s
  let q := pullback.fst f v
  let L' := (modulePullback q.toLRSHom.toShHom).obj L
  have hL' : IsInvertible (pullback f v).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) (pullback f v).IsSheaf)
      L' := Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry _ L hL
  let tF : pullback f e ⟶ pullback f v := pullback.lift (pullback.fst f e)
    (pullback.snd f e ≫ t) (by rw [pullback.condition, Category.assoc, ht])
  have htF : tF ≫ q = pullback.fst f e := pullback.lift_fst _ _ _
  have hi'q : ∀ k, pullback.map (i k ≫ f) v f v (i k) (𝟙 _) (𝟙 _) (by simp) (by simp) ≫ q =
      pullback.fst (i k ≫ f) v ≫ i k := (pullback_map_comp_fst f v <| i ·)
  obtain ⟨x, hx⟩ : ∃ x, f x = s :=
    (isConnected_preimage_singleton_of_isIso_structureSheafHom f s hO).nonempty
  obtain ⟨z, -, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := f) (g := e) x
    (IsLocalRing.closedPoint (S.residueField s))
    (hx.trans (Scheme.fromSpecResidueField_apply s _).symm)
  have : Nonempty ↥(pullback f e : Scheme.{u}) := ⟨z⟩
  obtain ⟨U', htU', hU'⟩ := exists_opens_isTrivial_of_injective_H1_of_comp_eq f hfp s hO Y i
    hflat hprop hfpk hOk hinj v t ht L'
    (fun k => ⟨modulePullbackObjIsoOfCompEq (hi'q k) L ≪≫ (htrivV k).some⟩)
    ⟨((modulePullbackComp tF.toLRSHom.toShHom q.toLRSHom.toShHom).app L).symm ≪≫
      (modulePullbackCongr (show tF.toLRSHom.toShHom ≫ q.toLRSHom.toShHom =
          (pullback.fst f e).toLRSHom.toShHom by rw [← comp_toLRSHom_toShHom, htF])).app L ≪≫
      (nonempty_iso_unit_of_descendsFromBase f L (S.residueField s) e hDe).some⟩
  exact ⟨U', htU', (descendsFromBase_comp_iff f L v U'.ι).2
    (descendsFromBase_of_nonempty_iso_unit (pullback.snd f v) L' U'.ι hU')⟩

/-- **[Stacks, Tag 0BF2].** Let `f : X ⟶ S` and the `i k ≫ f : Y k ⟶ S` (`k` in a finite type)
be flat, proper and of finite presentation with `𝒪_T ⟶ p_{T,*}𝒪` an isomorphism after every base
change `T ⟶ S`, the hypotheses of Tag 0BDP. Let `ℒ` be an invertible `𝒪_X`-module, `ℒ_k` its
pullback to `Y k`, and `Z`, `Z_k` descent loci (Tag 0BDP) of `ℒ` over `f` and of `ℒ_k` over
`i k ≫ f`. If `s ∈ Z` and `H¹(X_s, 𝒪) ⟶ ⊕_k H¹(Y_{k,s}, 𝒪)` is injective, then
`Z ∩ U = (⋂_k Z_k) ∩ U` (scheme theoretic intersection) for an open neighbourhood `U` of `s`: a
morphism `g : T ⟶ S` with image in `U` factors through `Z` if and only if it factors through every
`Z_k`.

`H¹(X_s, 𝒪)` is the degree-`1` cohomology of the `κ(s)`-linear derived global sections of
`𝒪_{X_s}`, and the `k`-th component of the map is
`Stacks.Cohomology.GlobalKunneth.sectionsPullbackMap` along the base change `Y_{k,s} ⟶ X_s` of
`i k`. -/
@[stacks 0BF2]
theorem IsDescentLocus.exists_factorsThrough_iff_forall_of_injective_H1
    [Flat f] [IsProper f] (hfp : FinitePresentation f)
    (hO : ∀ {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd f a).toLRSHom.toShHom))
    {ι : Type u} [Finite ι] (Y : ι → Scheme.{u}) (i : ∀ k, Y k ⟶ X)
    (hflat : ∀ k, Flat (i k ≫ f)) (hprop : ∀ k, IsProper (i k ≫ f))
    (hfpk : ∀ k, FinitePresentation (i k ≫ f))
    (hOk : ∀ k {T : Scheme.{u}} (a : T ⟶ S),
      IsIso (structureSheafHom (pullback.snd (i k ≫ f) a).toLRSHom.toShHom))
    (L : SheafOfModules.{u} (structureSheafRing X.toRingedSpace))
    [hL : IsInvertible X.presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) X.IsSheaf) L]
    {Z : Over S} (hZ : IsDescentLocus f L Z) {Zk : ι → Over S}
    (hZk : ∀ k, IsDescentLocus (i k ≫ f) ((modulePullback (i k).toLRSHom.toShHom).obj L) (Zk k))
    (s : S) (hs : s ∈ Set.range Z.hom)
    (hinj : ∀ c : (DerivedCategory.homologyFunctor
          (ModuleCat.{u} (baseRing (Spec (S.residueField s)).toRingedSpace)) 1).obj
        ((sectionsOverBase (pullback.snd f (S.fromSpecResidueField s)).toLRSHom.toShHom).obj
          (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
            (SheafOfModules.unit (structureSheafRing
              (pullback f (S.fromSpecResidueField s)).toRingedSpace))))),
      (∀ k, ((DerivedCategory.homologyFunctor _ 1).map
          (sectionsPullbackMap (pullback.snd f (S.fromSpecResidueField s)).toLRSHom.toShHom
            (pullback.map (i k ≫ f) (S.fromSpecResidueField s) f (S.fromSpecResidueField s)
              (i k) (𝟙 _) (𝟙 _) (by simp) (by simp)).toLRSHom.toShHom
            (DerivedCategory.Q.obj ((HomologicalComplex.single _ (ComplexShape.up ℤ) 0).obj
              (SheafOfModules.unit (structureSheafRing
                (pullback f (S.fromSpecResidueField s)).toRingedSpace)))))).hom c = 0) →
        c = 0) :
    ∃ U : S.Opens, s ∈ U ∧ ∀ {T : Scheme.{u}} (g : T ⟶ S), Set.range g ⊆ (U : Set S) →
      ((∃ h : T ⟶ Z.left, h ≫ Z.hom = g) ↔
        ∀ k, ∃ h : T ⟶ (Zk k).left, h ≫ (Zk k).hom = g) := by
  classical
  let e := S.fromSpecResidueField s
  let Lk : ∀ k, SheafOfModules.{u} (structureSheafRing (Y k).toRingedSpace) := fun k =>
    (modulePullback (i k).toLRSHom.toShHom).obj L
  have hLk : ∀ k, IsInvertible (Y k).presheaf
      (Presheaf.isSheaf_comp_of_isSheaf _ _ (forget₂ CommRingCat RingCat) (Y k).IsSheaf) (Lk k) :=
    fun k => Stacks.RingedSpace.modulePullback_isInvertible_algebraicGeometry _ L hL
  -- `Z ⊆ ⋂ Z_k`
  have hfwd : ∀ {T : Scheme.{u}} (g : T ⟶ S), DescendsFromBase f L g →
      ∀ k, ∃ h : T ⟶ (Zk k).left, h ≫ (Zk k).hom = g :=
    fun g hg k => ((hZk k).factorsThrough_iff g).2 (hg.comp_left f L (i k))
  -- the scheme theoretic intersection `W` of the `Z_k`, and the point `w₀` of `W` over `s`
  obtain ⟨W, _, hWg⟩ :=
    exists_isImmersion_factorsThrough_iff_forall Zk fun k => (hZk k).isImmersion
  have := hZ.isImmersion
  obtain ⟨tZ, htZ⟩ := exists_comp_eq_fromSpecResidueField_of_mem_range Z.hom s hs
  have hDe : DescendsFromBase f L e := (hZ.factorsThrough_iff e).1 ⟨tZ, htZ⟩
  obtain ⟨tW, htW⟩ := (hWg e).2 (hfwd e hDe)
  let pt : Spec (S.residueField s) := IsLocalRing.closedPoint (S.residueField s)
  let w₀ : W.left := tW pt
  have hw₀ : W.hom w₀ = s := apply_of_comp_eq_fromSpecResidueField htW pt
  -- every `ℒ_k` is free, of some rank, over an open neighbourhood `V` of `w₀`
  have hDW : ∀ k, DescendsFromBase (i k ≫ f) (Lk k) W.hom := fun k =>
    ((hZk k).factorsThrough_iff W.hom).1 ((hWg W.hom).1 ⟨𝟙 _, Category.id_comp _⟩ k)
  obtain ⟨V, n, hw₀V, hfree⟩ :=
    DescendsFromBase.exists_opens_forall_isFreeAlong (fun k => i k ≫ f) Lk hDW w₀
  let v : V.toScheme ⟶ S := V.ι ≫ W.hom
  let v₀ : V.toScheme := ⟨w₀, hw₀V⟩
  have hv₀ : v v₀ = s := by rwa [Scheme.Hom.comp_apply, Scheme.Opens.ι_apply]
  -- the point of `V` over `s`, with values in `κ(s)`
  have : IsImmersion v := inferInstanceAs (IsImmersion (V.ι ≫ W.hom))
  obtain ⟨t, ht⟩ := exists_comp_eq_fromSpecResidueField_of_mem_range v s ⟨v₀, hv₀⟩
  -- every `ℒ_k` is trivial over `Y k ×_S V`, so the case of trivial faces applies over `V`
  obtain ⟨U', htU', hDU'⟩ := exists_opens_descendsFromBase_of_isTrivial_of_injective_H1 f hfp s
    (hO e) Y i hflat hprop hfpk (fun k => hOk k e) hinj L hDe v t ht fun k => by
      obtain ⟨y, hy⟩ : ∃ y, (i k ≫ f) y = s :=
        (isConnected_preimage_singleton_of_isIso_structureSheafHom _ s (hOk k e)).nonempty
      exact (hfree k).isTrivial_modulePullback_fst (i k ≫ f) (Lk k) (hy.trans hv₀.symm)
  -- the open `U` of `S` cutting `U'` out of `W`
  obtain ⟨U₀, hpre, hU₀⟩ := DescendsFromBase.exists_opens_forall_of_isOpenImmersion f L
    (w := W.hom) (j := U'.ι ≫ V.ι) (by rwa [Category.assoc])
  refine ⟨U₀, ?_, fun {T} g hg => ⟨fun H => hfwd g ((hZ.factorsThrough_iff g).1 H),
    fun H => ?_⟩⟩
  · have hmem : V.ι (t pt) ∈ W.hom ⁻¹' U₀ := by
      rw [hpre]
      exact ⟨⟨t pt, Set.range_subset_iff.1 htU' pt⟩, rfl⟩
    have hs' : W.hom (V.ι (t pt)) = s := by
      rw [← Scheme.Hom.comp_apply]
      exact apply_of_comp_eq_fromSpecResidueField ht pt
    rw [← hs']
    exact hmem
  · obtain ⟨h, rfl⟩ := (hWg g).2 H
    exact (hZ.factorsThrough_iff _).2 (hU₀ h hg)

end AlgebraicGeometry

end
