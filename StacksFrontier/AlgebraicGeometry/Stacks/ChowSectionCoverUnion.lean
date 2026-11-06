module

public import StacksFrontier.AlgebraicGeometry.Stacks.ChowRelativeSections
public import StacksFrontier.AlgebraicGeometry.Stacks.LiftingAffinesCoproduct
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductSeparated
public import StacksFrontier.AlgebraicGeometry.Spaces.ChowLemma.CoproductZariskiCover
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCoverAlgebraic
public import StacksFrontier.CategoryTheory.Sites.Modules.LocallyRingedSites.OneIsNeverZero

/-!
# Sections over finitely many proper modifications, as one

Let `f : 𝒳 ⟶ Y` be a separated 1-morphism with all its values in an open `W ⊆ Y`. A section of
`f` over a proper modification `p : Y' ⟶ Y`, that is a 1-morphism `x : p⁻¹(W) ⟶ 𝒳` over `Y`, is a
proper compactifiable cover of `f` (`CompactifiableCover.ofSection`). Finitely many of them
assemble into one: over the disjoint union `∐ Y'ᵢ` the sections glue, the summands of a
coproduct of sheaves being open and pairwise disjoint (the coproduct is van Kampen). This is the
disjoint union which the source's single cover in [Stacks, Tag 0CQ7] amounts to.

## Main results

* `AlgebraicGeometry.Space.isEmpty_of_cofan_inj_app_eq`: two sections of distinct summands of a
  coproduct of sheaves with the same image lie over an empty scheme.
* `AlgebraicGeometry.Stack.AlgebraicStacks.exists_section_union`: finitely many sections over
  proper modifications give one whose image contains all of theirs.

## References

* [Stacks Project, Tag 0CQ7](https://stacks.math.columbia.edu/tag/0CQ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u w

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **An object of the site over which the empty sieve covers is empty.** -/
theorem isEmpty_of_bot_mem_topology {V : BigFppfOver B S hS}
    (h : (⊥ : Sieve V) ∈ BigFppfOver.topology B S hS V) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj V) := by
  have hsub := Stacks.Sheaves.LocallyRingedSite.subsingleton_sections_of_bot_mem
    ((BigFppfOver.topology B S hS).yoneda.obj
      (BigFppfOver.sigmaObj B S hS (fun _ : ULift.{u} Bool => V))) h
  have he : BigFppfOver.sigmaIncl B S hS (fun _ : ULift.{u} Bool => V) ⟨false⟩ =
      BigFppfOver.sigmaIncl B S hS (fun _ : ULift.{u} Bool => V) ⟨true⟩ :=
    hsub.elim _ _
  exact SpacesEtale.isEmpty_of_comp_eq_cofan (L := ULift.{u} Bool) (fun _ => V)
    (BigFppfOver.sigmaIncl B S hS _) (BigFppfOver.isColimit_sigmaCofan B S hS _)
    (k := ⟨false⟩) (l := ⟨true⟩) (by simp) (𝟙 V) (𝟙 V) (by rw [Category.id_comp, he,
      Category.id_comp])

section Cofan

variable {K : Type u} {F : K → Sheaf (BigFppfOver.topology B S hS) (Type u)}
  {G : Sheaf (BigFppfOver.topology B S hS) (Type u)} (ι : ∀ k, F k ⟶ G)
  (hc : IsColimit (Cofan.mk G ι))

include hc

/-- **The summand inclusions of a coproduct of sheaves are injective on sections.** -/
theorem cofan_inj_app_injective (k : K) (V : (BigFppfOver B S hS)ᵒᵖ) :
    Function.Injective ((ι k).hom.app V) := by
  have := BigFppfOver.hasSheafify_type B S hS
  have : HasColimitsOfShape (Discrete K) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    functorCategoryHasColimitsOfShape
  have hm : Mono (ι k) := mono_of_cofan_isVanKampen
    (isVanKampenColimit_of_isColimit_sheafOfTypes _ hc) ⟨k⟩
  have hm' : Mono (ι k).hom := (sheafToPresheaf _ _).map_mono (ι k)
  exact (mono_iff_injective _).1 (inferInstance : Mono ((ι k).hom.app V))

/-- **Two sections of distinct summands of a coproduct of sheaves with the same image lie over
an empty scheme.** -/
theorem isEmpty_of_cofan_inj_app_eq {k l : K} (hkl : k ≠ l) {V : BigFppfOver B S hS}
    (a : (F k).obj.obj (op V)) (b : (F l).obj.obj (op V))
    (h : (ι k).hom.app _ a = (ι l).hom.app _ b) :
    IsEmpty ((BigFppfOver.toScheme B S hS).obj V) := by
  have := BigFppfOver.hasSheafify_type B S hS
  have : HasColimitsOfShape (Discrete K) ((BigFppfOver B S hS)ᵒᵖ ⥤ Type u) :=
    functorCategoryHasColimitsOfShape
  have hpb := isPullback_initial_to_of_cofan_isVanKampen
    (isVanKampenColimit_of_isColimit_sheafOfTypes _ hc) ⟨k⟩ ⟨l⟩ (by simpa using hkl)
  have hpb' := (hpb.map (sheafToPresheaf _ _)).map ((evaluation _ _).obj (op V))
  obtain ⟨z, -, -⟩ := Types.exists_of_isPullback hpb' a b h
  exact isEmpty_of_bot_mem_topology
    (Stacks.Sheaves.LocallyRingedSite.bot_mem_of_isInitial initialIsInitial z)

end Cofan

end AlgebraicGeometry.Space

namespace AlgebraicGeometry.Stack.AlgebraicStacks

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Finitely many sections over proper modifications assemble into one.** Let `f : 𝒳 ⟶ Y` be
separated with its values in an open `W ⊆ Y`, and let `xₖ : pₖ⁻¹(W) ⟶ 𝒳` be 1-morphisms over `Y`
out of the inverse images of `W` under finitely many proper `pₖ : Y'ₖ ⟶ Y`. Over the coproduct
`Y' = ∐ Y'ₖ`, proper over `Y` by the sum `p` of the `pₖ`, the `xₖ` glue to a 1-morphism
`x : p⁻¹(W) ⟶ 𝒳` over `Y`, and the cover `CompactifiableCover.ofSection` of `x` contains every one
of the `xₖ`. -/
theorem exists_section_union {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (hY : IsAlgebraicSpace B S hS Y) {𝒳 : AlgebraicStacks.{u, w} B S hS}
    (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY) (hf : IsSeparated B S hS f)
    (W : Subfunctor Y) (hW : Space.IsOpenSubspace B S hS W)
    (hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ)))
    {K : Type u} [Finite K] (Y' : K → (BigFppfOver B S hS)ᵒᵖ ⥤ Type u)
    (hY' : ∀ k, IsAlgebraicSpace B S hS (Y' k)) (p : ∀ k, Y' k ⟶ Y)
    (hp : ∀ k, Space.IsProper B S hS (p k))
    (x : ∀ k, algebraicSpaceStack.{u, w} B S hS (W.preimage (p k)).toFunctor
      (Space.isOpenSubspace_preimage B S hS (p k) W hY (hY' k) hW).1 ⟶ 𝒳)
    (hx : ∀ k, Nonempty (x k ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS
      (Space.isOpenSubspace_preimage B S hS (p k) W hY (hY' k) hW).1 hY
        ((W.preimage (p k)).ι ≫ p k))) :
    ∃ (Y'' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY'' : IsAlgebraicSpace B S hS Y'')
      (p' : Y'' ⟶ Y) (hp' : Space.IsProper B S hS p')
      (x' : algebraicSpaceStack.{u, w} B S hS (W.preimage p').toFunctor
        (Space.isOpenSubspace_preimage B S hS p' W hY hY'' hW).1 ⟶ 𝒳)
      (hx' : Nonempty (x' ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS
        (Space.isOpenSubspace_preimage B S hS p' W hY hY'' hW).1 hY ((W.preimage p').ι ≫ p'))),
      ∀ k, (CompactifiableCover.ofSection hY (hY' k) f hf W hW hfW (p k) (hp k) (x k)
          (hx k)).image ⊆
        (CompactifiableCover.ofSection hY hY'' f hf W hW hfW p' hp' x' hx').image := by
  classical
  have := BigFppfOver.hasSheafify_type B S hS
  let FS : K → Sheaf (BigFppfOver.topology B S hS) (Type u) := fun k => ⟨Y' k, (hY' k).isSheaf⟩
  let G : Sheaf (BigFppfOver.topology B S hS) (Type u) := ∐ FS
  let ι : ∀ k, FS k ⟶ G := Sigma.ι FS
  have hc : IsColimit (Cofan.mk G ι) := coproductIsCoproduct FS
  have hG : IsAlgebraicSpace B S hS G.obj :=
    isAlgebraicSpace_coproduct_of_admitsCoproductIndex B S hS Y' hY' G ι hc
  let YS : Sheaf (BigFppfOver.topology B S hS) (Type u) := ⟨Y, hY.isSheaf⟩
  let PS : G ⟶ YS := Sigma.desc (fun k => (⟨p k⟩ : FS k ⟶ YS))
  have hιP : ∀ k, (ι k).hom ≫ PS.hom = p k := fun k =>
    congrArg (fun φ : FS k ⟶ YS => φ.hom)
      (Sigma.ι_desc (f := FS) (fun k => (⟨p k⟩ : FS k ⟶ YS)) k)
  have hPp : Space.IsProper B S hS PS.hom :=
    Space.isProper_of_isColimit_cofan B S hS ι hc (fun k => hY' k) hG hY PS.hom
      (fun k => by rw [hιP k]; exact hp k)
  let Wp := W.preimage PS.hom
  have hWp : Space.IsOpenSubspace B S hS Wp :=
    Space.isOpenSubspace_preimage B S hS PS.hom W hY hG hW
  let Wk : ∀ k, Subfunctor (Y' k) := fun k => Wp.preimage (ι k).hom
  have hWk : ∀ k, Space.IsOpenSubspace B S hS (Wk k) := fun k =>
    Space.isOpenSubspace_preimage B S hS (ι k).hom Wp hG (hY' k) hWp
  have hle : ∀ k, Wk k ≤ W.preimage (p k) := by
    intro k T y hy
    show (p k).app T y ∈ W.obj T
    rwa [← hιP k]
  have hpre : ∀ k, Space.IsOpenSubspace B S hS (W.preimage (p k)) := fun k =>
    Space.isOpenSubspace_preimage B S hS (p k) W hY (hY' k) hW
  let xk : ∀ k, algebraicSpaceStack.{u, w} B S hS (Wk k).toFunctor (hWk k).1 ⟶ 𝒳 := fun k =>
    algebraicSpaceStackMap.{u, w} B S hS (hWk k).1 (hpre k).1 (Subfunctor.homOfLe (hle k)) ≫ x k
  let T : AlgebraicSpaces B S hS := ⟨Wp.toFunctor, hWp.1⟩
  let T' : K → AlgebraicSpaces B S hS := fun k => ⟨(Wk k).toFunctor, (hWk k).1⟩
  let e : ∀ k, T' k ⟶ T := fun k => ObjectProperty.homMk (Wp.fromPreimage (ι k).hom)
  have hZ := (Space.isZariskiCover_iff_iUnion_points B S hS G.obj hG K _
    (fun k => Space.isOpenSubspace_range_cofan_inj ι hc k (hY' k))).1
    (Space.isZariskiCover_range_cofan_inj ι hc fun k => hY' k)
  have hcovG : ∀ z : Space.points B S hS G.obj, ∃ k z',
      Space.pointsMap B S hS (Y' k) (ι k).hom z' = z := by
    intro z
    have hz : z ∈ ⋃ k, Set.range (Space.pointsMap B S hS
        (Subfunctor.range (ι k).hom).toFunctor (Subfunctor.range (ι k).hom).ι) := by
      simp [hZ]
    obtain ⟨k, r, rfl⟩ := Set.mem_iUnion.1 hz
    have : Mono (ι k).hom := Space.mono_of_isOpenImmersion B S hS (ι k).hom
      (coproductIncl_isOpenImmersion B S hS FS G ι hc k)
    obtain ⟨z', rfl⟩ : ∃ z', Space.pointsMap B S hS _ (Subfunctor.toRange (ι k).hom) z' = r :=
      ⟨Space.pointsMap B S hS _ (inv (Subfunctor.toRange (ι k).hom)) r, by
        rw [← Space.pointsMap_comp_apply, IsIso.inv_hom_id, Space.pointsMap_id]; rfl⟩
    exact ⟨k, z', by rw [← Space.pointsMap_comp_apply, Subfunctor.toRange_ι]⟩
  have he : Space.IsEtaleCovering B S hS (fun k => (T' k).obj) (fun k => (e k).hom) := by
    refine ⟨hWp.1, fun k => (hWk k).1, fun k => ?_, ?_⟩
    · have _hsbc : MorphismProperty.IsStableUnderBaseChange
          (MorphismProperty.presheaf (MorphismProperty.inverseImage
            (@_root_.AlgebraicGeometry.IsOpenImmersion.{u} : MorphismProperty Scheme.{u})
            (BigFppfOver.toScheme B S hS))) :=
        MorphismProperty.relative_isStableUnderBaseChange _
      exact Space.isEtale_of_isOpenImmersion B S hS (MorphismProperty.of_isPullback
        (Subfunctor.isPullback_preimage (ι k).hom Wp).flip
        (coproductIncl_isOpenImmersion B S hS FS G ι hc k))
    · refine Set.eq_univ_of_forall fun y => ?_
      obtain ⟨k, z', hz'⟩ := hcovG (Space.pointsMap B S hS _ Wp.ι y)
      have hmem : z' ∈ Set.range (Space.pointsMap B S hS (Wk k).toFunctor (Wk k).ι) := by
        rw [Space.range_pointsMap_preimage_ι, Set.mem_preimage, hz']
        exact ⟨y, rfl⟩
      obtain ⟨t, rfl⟩ := hmem
      refine Set.mem_iUnion.2 ⟨k, t, ?_⟩
      refine Space.pointsMap_injective_of_mono B S hS Wp.ι ?_
      show Space.pointsMap B S hS _ Wp.ι
        (Space.pointsMap B S hS _ (Wp.fromPreimage (ι k).hom) t) = _
      rw [← Space.pointsMap_comp_apply, Subfunctor.fromPreimage_ι, Space.pointsMap_comp_apply, hz']
  have hinj : ∀ (k : K) (V : BigFppfOver B S hS) (a a' : (T' k).obj.obj (op V)),
      (e k).hom.app _ a = (e k).hom.app _ a' → a = a' := fun k _ _ _ h =>
    Subtype.ext (Space.cofan_inj_app_injective ι hc k _ (congrArg Subtype.val h))
  have hdisj : ∀ (k l : K), k ≠ l → ∀ (V : BigFppfOver B S hS) (a : (T' k).obj.obj (op V))
      (b : (T' l).obj.obj (op V)), (e k).hom.app _ a = (e l).hom.app _ b →
        IsEmpty ((BigFppfOver.toScheme B S hS).obj V) := fun k l hkl V a b h =>
    Space.isEmpty_of_cofan_inj_app_eq ι hc hkl a.1 b.1 (congrArg Subtype.val h)
  obtain ⟨Gx, ψ, -⟩ := exists_hom_of_isEtaleCovering he (disjointGluing e hinj hdisj xk)
  have hGx : Gx ≫ f = algebraicSpaceStackMap.{u, w} B S hS hWp.1 hY (Wp.ι ≫ PS.hom) := by
    let r := representingMap B S hS _ _ Wp.toFunctor Y
      (StacksRepresentableCFG.EquivalenceOver.refl _)
      (StacksRepresentableCFG.EquivalenceOver.refl _) (Gx ≫ f).hom
    have hr : algebraicSpaceStackMap.{u, w} B S hS hWp.1 hY r = Gx ≫ f :=
      algebraicSpaceStackMap_representingMap hWp.1 hY (Gx ≫ f)
    suffices hrr : r = Wp.ι ≫ PS.hom by rw [← hr, hrr]
    refine Space.hom_ext_of_isFppfCovering B S hS (fun k => (T' k).obj) (fun k => (e k).hom)
      (Space.isFppfCovering_of_isEtaleCovering B S hS he) hY.isSheaf fun k => ?_
    refine eq_of_algebraicSpaceStackMap_eq (hWk k).1 hY ?_
    obtain ⟨ek⟩ := hx k
    have hψ : algebraicSpaceStackMap.{u, w} B S hS (hWk k).1 hWp.1 (e k).hom ≫ Gx ≅ xk k :=
      Bicategory.InducedBicategory.isoMk (CatFiberedInGroupoids.twoIso (ψ k).hom)
    have hgeom : Subfunctor.homOfLe (hle k) ≫ (W.preimage (p k)).ι ≫ p k =
        (e k).hom ≫ Wp.ι ≫ PS.hom := by
      have hfp : (e k).hom ≫ Wp.ι = (Wk k).ι ≫ (ι k).hom := Subfunctor.fromPreimage_ι _ _
      rw [← Category.assoc, Subfunctor.homOfLe_ι, ← hιP k, ← Category.assoc ((e k).hom), hfp,
        Category.assoc]
    rw [algebraicSpaceStackMap_comp_eq (hWk k).1 hWp.1 hY, hr]
    refine eq_of_iso_algebraicSpaceStack hY ((Bicategory.associator _ _ _).symm ≪≫
      Bicategory.whiskerRightIso hψ f ≪≫ Bicategory.associator _ _ _ ≪≫
      Bicategory.whiskerLeftIso _ ek ≪≫ eqToIso ?_)
    rw [← algebraicSpaceStackMap_comp_eq, hgeom]
  refine ⟨G.obj, hG, PS.hom, hPp, Gx, ⟨eqToIso hGx⟩, fun k => ?_⟩
  rintro _ ⟨z₀, rfl⟩
  let z : Space.points B S hS (W.preimage (p k)).toFunctor := z₀
  show Space.pointsMap B S hS (W.preimage (p k)).toFunctor ((W.preimage (p k)).ι ≫ p k) z ∈
    Set.range (Space.pointsMap B S hS Wp.toFunctor (Wp.ι ≫ PS.hom))
  set t := Space.pointsMap B S hS _ (W.preimage (p k)).ι z
  have ht : Space.pointsMap B S hS _ (p k) t ∈
      Set.range (Space.pointsMap B S hS W.toFunctor W.ι) :=
    (Space.range_pointsMap_preimage_ι B S hS (p k) W).le ⟨z, rfl⟩
  have hy : Space.pointsMap B S hS _ (ι k).hom t ∈ Set.range (Space.pointsMap B S hS _ Wp.ι) := by
    rwa [Space.range_pointsMap_preimage_ι, Set.mem_preimage, ← Space.pointsMap_comp_apply, hιP k]
  obtain ⟨y, hy⟩ := hy
  refine ⟨y, ?_⟩
  rw [Space.pointsMap_comp_apply, hy, ← Space.pointsMap_comp_apply, hιP k,
    Space.pointsMap_comp_apply]

/-- **A section cover of a set of points**: one section `x : p⁻¹(W) ⟶ 𝒳` of `f` over a proper
`p : Y' ⟶ Y` whose compactifiable cover `CompactifiableCover.ofSection` contains the set. -/
def HasSectionCovers {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (hf : IsSeparated B S hS f) (W : Subfunctor Y) (hW : Space.IsOpenSubspace B S hS W)
    (hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ)))
    (P : Set (Space.points B S hS Y)) : Prop :=
  ∃ (Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u) (hY' : IsAlgebraicSpace B S hS Y') (p : Y' ⟶ Y)
    (hp : Space.IsProper B S hS p)
    (x : algebraicSpaceStack.{u, w} B S hS (W.preimage p).toFunctor
      (Space.isOpenSubspace_preimage B S hS p W hY hY' hW).1 ⟶ 𝒳)
    (hx : Nonempty (x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS
      (Space.isOpenSubspace_preimage B S hS p W hY hY' hW).1 hY ((W.preimage p).ι ≫ p))),
    P ⊆ (CompactifiableCover.ofSection hY hY' f hf W hW hfW p hp x hx).image

/-- **A single proper compactifiable cover of a set of points.** -/
def HasCompactifiableCover {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {𝒳 : AlgebraicStacks.{u, w} B S hS} (f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY)
    (P : Set (Space.points B S hS Y)) : Prop :=
  ∃ c : CompactifiableCover hY f, P ⊆ c.image

namespace HasSectionCovers

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}
  {hf : IsSeparated B S hS f} {W : Subfunctor Y} {hW : Space.IsOpenSubspace B S hS W}
  {hfW : ∀ ξ, algebraicSpaceStackSection f ξ ∈ W.obj (op (𝒳.val.val.p.obj ξ))}

/-- A section cover of a set covers its subsets. -/
theorem mono {P Q : Set (Space.points B S hS Y)} (h : HasSectionCovers hY f hf W hW hfW Q)
    (hPQ : P ⊆ Q) : HasSectionCovers hY f hf W hW hfW P := by
  obtain ⟨Y', hY', p, hp, x, hx, h⟩ := h
  exact ⟨Y', hY', p, hp, x, hx, hPQ.trans h⟩

/-- A section is a section cover of its image. -/
theorem of_section {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY' : IsAlgebraicSpace B S hS Y')
    (p : Y' ⟶ Y) (hp : Space.IsProper B S hS p)
    (x : algebraicSpaceStack.{u, w} B S hS (W.preimage p).toFunctor
      (Space.isOpenSubspace_preimage B S hS p W hY hY' hW).1 ⟶ 𝒳)
    (hx : Nonempty (x ≫ f ≅ algebraicSpaceStackMap.{u, w} B S hS
      (Space.isOpenSubspace_preimage B S hS p W hY hY' hW).1 hY ((W.preimage p).ι ≫ p)))
    {P : Set (Space.points B S hS Y)}
    (hP : P ⊆ (CompactifiableCover.ofSection hY hY' f hf W hW hfW p hp x hx).image) :
    HasSectionCovers hY f hf W hW hfW P :=
  ⟨Y', hY', p, hp, x, hx, hP⟩

/-- **Finitely many section covers combine into one.** -/
theorem iUnion {κ : Type*} [Finite κ] (P : κ → Set (Space.points B S hS Y))
    (hP : ∀ k, HasSectionCovers hY f hf W hW hfW (P k)) :
    HasSectionCovers hY f hf W hW hfW (⋃ k, P k) := by
  obtain ⟨n, ⟨eq⟩⟩ := Finite.exists_equiv_fin κ
  choose Y' hY' p hp x hx hsub using hP
  let a : ULift.{u} (Fin n) → κ := fun k => eq.symm k.down
  obtain ⟨Y'', hY'', p', hp', x', hx', hall⟩ := exists_section_union hY f hf W hW hfW
    (K := ULift.{u} (Fin n)) (fun k => Y' (a k)) (fun k => hY' (a k)) (fun k => p (a k))
    (fun k => hp (a k)) (fun k => x (a k)) (fun k => hx (a k))
  refine ⟨Y'', hY'', p', hp', x', hx', fun y hy => ?_⟩
  obtain ⟨k, hk⟩ := Set.mem_iUnion.1 hy
  have hk' : a ⟨eq k⟩ = k := eq.symm_apply_apply k
  have h := hall ⟨eq k⟩
  rw [hk'] at h
  exact h (hsub k hk)

/-- The empty set has a section cover. -/
theorem empty : HasSectionCovers hY f hf W hW hfW ∅ := by
  simpa using iUnion (κ := PEmpty.{1}) (hY := hY) (f := f) (hf := hf) (hW := hW) (hfW := hfW)
    (fun k : PEmpty.{1} => k.elim) (fun k : PEmpty.{1} => k.elim)

/-- Two section covers combine into one. -/
theorem union {P Q : Set (Space.points B S hS Y)} (hP : HasSectionCovers hY f hf W hW hfW P)
    (hQ : HasSectionCovers hY f hf W hW hfW Q) : HasSectionCovers hY f hf W hW hfW (P ∪ Q) := by
  have h := iUnion (κ := Bool) (fun b => bif b then Q else P) (fun b => by cases b <;> assumption)
  refine h.mono fun y hy => ?_
  rcases hy with hy | hy
  · exact Set.mem_iUnion.2 ⟨false, hy⟩
  · exact Set.mem_iUnion.2 ⟨true, hy⟩

/-- Finitely many section covers, over a finite set of indices, combine into one. -/
theorem biUnion {κ : Type*} (s : Set κ) (hs : s.Finite) (P : κ → Set (Space.points B S hS Y))
    (hP : ∀ k ∈ s, HasSectionCovers hY f hf W hW hfW (P k)) :
    HasSectionCovers hY f hf W hW hfW (⋃ k ∈ s, P k) := by
  induction s, hs using Set.Finite.induction_on with
  | empty => simpa using (empty : HasSectionCovers hY f hf W hW hfW ∅)
  | @insert a s _ _ ih =>
    rw [Set.biUnion_insert]
    exact union (hP a (Set.mem_insert a s))
      (ih fun k hk => hP k (Set.mem_insert_of_mem a hk))

/-- A section cover is a single proper compactifiable cover. -/
theorem hasCompactifiableCover {P : Set (Space.points B S hS Y)}
    (h : HasSectionCovers hY f hf W hW hfW P) : HasCompactifiableCover hY f P := by
  obtain ⟨Y', hY', p, hp, x, hx, h⟩ := h
  exact ⟨_, h⟩

end HasSectionCovers

namespace HasCompactifiableCover

variable {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY : IsAlgebraicSpace B S hS Y}
  {𝒳 : AlgebraicStacks.{u, w} B S hS} {f : 𝒳 ⟶ algebraicSpaceStack.{u, w} B S hS Y hY}

/-- **Single proper compactifiable covers push forward along proper morphisms.** If
`a : 𝒳' ⟶ 𝒳` and `p : Y' ⟶ Y` are proper with `a ≫ f ≅ f' ≫ p`, a set of points of `Y` inside the
image under `p` of a set with a single proper compactifiable cover for `f'` has one for `f`. -/
theorem of_proper {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hY' : IsAlgebraicSpace B S hS Y'}
    {𝒳' : AlgebraicStacks.{u, w} B S hS} {f' : 𝒳' ⟶ algebraicSpaceStack.{u, w} B S hS Y' hY'}
    (p : Y' ⟶ Y) (hp : Space.IsProper B S hS p) (a : 𝒳' ⟶ 𝒳) (ha : IsProper B S hS a)
    (e : a ≫ f ≅ f' ≫ algebraicSpaceStackMap.{u, w} B S hS hY' hY p)
    {P' : Set (Space.points B S hS Y')} (h : HasCompactifiableCover hY' f' P')
    {P : Set (Space.points B S hS Y)} (hP : P ⊆ Space.pointsMap B S hS Y' p '' P') :
    HasCompactifiableCover hY f P := by
  obtain ⟨c, hc⟩ := h
  refine ⟨c.pushforward p hp a ha e, fun y hy => ?_⟩
  obtain ⟨y', hy', rfl⟩ := hP hy
  rw [CompactifiableCover.image_pushforward]
  exact ⟨y', hc hy', rfl⟩

/-- **Single proper compactifiable covers descend along a proper base change.** If `g : Y' ⟶ Y`
is proper, a set of points of `Y` inside the image under `g` of a set with a single proper
compactifiable cover for the base change of `f` along `g` has one for `f`. -/
theorem of_baseChange {Y' : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY' : IsAlgebraicSpace B S hS Y')
    (g : Y' ⟶ Y) (hg : Space.IsProper B S hS g) {P' : Set (Space.points B S hS Y')}
    (h : HasCompactifiableCover hY'
      (twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hY' hY g) f).fst P')
    {P : Set (Space.points B S hS Y)} (hP : P ⊆ Space.pointsMap B S hS Y' g '' P') :
    HasCompactifiableCover hY f P := by
  let Q := twoFibreProductSquare B S hS (algebraicSpaceStackMap.{u, w} B S hS hY' hY g) f
  have ha : IsProper B S hS Q.snd :=
    isProper_baseChange B S hS (algebraicSpaceStackMap.{u, w} B S hS hY' hY g) f Q.swap
      (Bicategory.isTwoFibreProduct_swap (isTwoFibreProduct_twoFibreProductSquare B S hS _ f))
      ((isProper_algebraicSpaceStackMap_iff.{u, w} B S hS hY' hY g).2 hg)
  exact of_proper g hg Q.snd ha Q.iso.symm h hP

end HasCompactifiableCover

end AlgebraicGeometry.Stack.AlgebraicStacks

end
