module

public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.Big
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.Subcanonical
public import StacksFrontier.AlgebraicGeometry.ProEtale.WLocal.WContractibleCoverCardinality
public import StacksFrontier.AlgebraicGeometry.Size.Affine
public import StacksFrontier.CategoryTheory.Sites.Representable.CoproductYonedaDesc
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible
public import StacksFrontier.CategoryTheory.Sites.WeaklyContractible.WContractibleRings

/-!
# Clopen Zariski refinements and weak contractibility

A finite family of open immersions into a scheme whose images are pairwise disjoint and cover
it — a *clopen decomposition cover* — is the shape of refinement that detects weak
contractibility. Over such a family a compatible family of sections of a sheaf is
automatically compatible: two distinct members meet only in a scheme with empty underlying
space, over which every sheaf of sets has a single section. So an object all of whose covering
sieves are refined by a clopen decomposition cover is weakly contractible.

For an affine object of a chosen big pro-étale site this refinement property holds as soon as
its ring of global sections is w-contractible. The passage is along the isomorphism with the
spectrum of that ring: a covering sieve of the object yields a pro-étale covering sieve of the
spectrum, w-contractibility refines it by a clopen decomposition, and the members of that
decomposition are open subschemes of the object, hence small enough to belong to the chosen
big site again.

## Main results

* `CategoryTheory.GrothendieckTopology.isWeaklyContractible_of_clopenRefinements`: an object
  each of whose covering sieves has a clopen decomposition refinement is weakly
  contractible.
* `CategoryTheory.GrothendieckTopology.surjective_sections_over_of_clopenRefinements`: the
  same criterion on the slice site, at its final object.
* `ProetaleWContractible.IsClopenDecompositionCover.comp_iso`: a clopen decomposition cover
  transports along an isomorphism of its target.
* `ProetaleWContractible.isWContractible_of_isWeaklyContractible`: an affine weakly
  contractible object of the pro-étale site has w-contractible global sections.
* `AlgebraicGeometry.ProEtale.exists_clopenRefinement_of_isWContractible`: every covering
  sieve of an affine object with w-contractible global sections is refined by a clopen
  decomposition cover inside the chosen big site.
* `AlgebraicGeometry.ProEtale.BigProetaleSite.bot_mem_topology_of_isEmpty` and
  `BigProetaleSite.sieve_ofArrows_mem_topology_of_isClopenDecompositionCover`: the empty family
  covers an object with empty underlying space, and a clopen decomposition cover of an object
  of the chosen big site generates a covering sieve.
* `AlgebraicGeometry.ProEtale.BigProetaleSite.isWeaklyContractible_of_clopenRefinements` and
  `BigProetaleSite.isWContractible_of_isWeaklyContractible`: the two remaining implications
  relating clopen refinements, weak contractibility and w-contractible global sections in the
  chosen big site.
* `AlgebraicGeometry.ProEtale.isWContractible_globalSections_tfae`: for an affine object of a
  chosen big pro-étale site the three conditions are equivalent.

## Implementation notes

The criterion is stated for an arbitrary site equipped with a functor to schemes, since the
pro-étale sites it is applied to are full subcategories of slices and the decomposition lives
in the underlying schemes. Two hypotheses replace what is automatic for a subcategory of
schemes: that a sieve is covering as soon as the underlying scheme has empty space, and that
the functor reflects monomorphisms.

## References

* [Stacks Project, Tag 098F](https://stacks.math.columbia.edu/tag/098F)
* [Stacks Project, Tag 098H](https://stacks.math.columbia.edu/tag/098H)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite

universe v w u

namespace CategoryTheory.GrothendieckTopology

variable {C : Type w} [Category.{v} C]

universe t

/-- **Sections form of the clopen-refinement criterion, at any value universe.** If every
covering sieve of `U` is refined by a finite family of morphisms whose images in schemes form a
disjoint clopen cover, then a locally surjective morphism of sheaves of types is surjective on
sections over `U`, whatever the universe of those types.

Compatibility of a family of sections indexed by such a refinement is automatic: distinct
members are disjoint, so their fibre products have empty underlying space, and the two
hypotheses `hbot` and `hmono` make the sheaf condition over the refinement an isomorphism.

The value universe of the sheaves is free of the morphism universe of the site, which is needed
because weak contractibility as a property of the site is stated at the morphism universe,
while abelian sheaves on a site whose objects exceed its morphisms take values in a strictly
larger universe. -/
theorem surjective_sections_of_clopenRefinements (J : GrothendieckTopology C)
    (Q : C ⥤ AlgebraicGeometry.Scheme.{u}) (U : C)
    (hbot : ∀ Z, IsEmpty (Q.obj Z).carrier → (⊥ : Sieve Z) ∈ J Z)
    (hmono : ∀ {X Y : C} (f : X ⟶ Y), Mono (Q.map f) → Mono f)
    (href : ∀ S : Sieve U, S ∈ J U →
      ∃ (n : ℕ) (V : Fin n → C) (f : (i : Fin n) → V i ⟶ U),
        ProetaleWContractible.IsClopenDecompositionCover
          (fun i ↦ Q.obj (V i)) (fun i ↦ Q.map (f i)) ∧
        Sieve.ofArrows V f ∈ J U ∧ ∀ i, S.arrows (f i))
    (F G : Sheaf J (Type t)) (φ : F ⟶ G) (hφ : Sheaf.IsLocallySurjective φ) :
    Function.Surjective (φ.hom.app (op U)) := by
  classical
  intro s
  obtain ⟨n, V, f, hdec, hcover, hmem⟩ := href _ (hφ.imageSieve_mem s)
  choose t ht using fun i ↦ (hmem i : ∃ _, _)
  have hcompat : Presieve.Arrows.Compatible F.obj f t := by
    intro i j Z gi gj hcomp
    by_cases hij : i = j
    · subst hij
      have : Mono (f i) := hmono (f i) (hdec.openImmersion i).mono
      rw [(cancel_mono (f i)).1 hcomp]
    · have hZ : IsEmpty (Q.obj Z).carrier := by
        refine ⟨fun z ↦ ?_⟩
        have heq : (Q.map (f i)).base ((Q.map gi).base z) =
            (Q.map (f j)).base ((Q.map gj).base z) := by
          have hh := congrArg (fun q ↦ (Q.map q).base z) hcomp
          rw [Functor.map_comp, Functor.map_comp] at hh
          simpa only [AlgebraicGeometry.Scheme.Hom.comp_base,
            ConcreteCategory.comp_apply] using hh
        have hmemi : (Q.map (f i)).base ((Q.map gi).base z) ∈
          Set.range (Q.map (f i)).base := ⟨_, rfl⟩
        have hmemj : (Q.map (f i)).base ((Q.map gi).base z) ∈
          Set.range (Q.map (f j)).base := heq ▸ ⟨_, rfl⟩
        exact (hdec.disjoint i j hij).le_bot ⟨hmemi, hmemj⟩
      let _ : Unique (F.obj.obj (op Z)) :=
        Types.isTerminalEquivUnique _ (Sheaf.isTerminalOfBotCover F Z (hbot Z hZ))
      exact Subsingleton.elim _ _
  have hsh (H : Sheaf J (Type t)) : Presieve.IsSheafFor H.obj (Presieve.ofArrows V f) := by
    rw [Presieve.isSheafFor_iff_generate]; exact H.property.isSheafFor _ hcover
  have hFsh := (Presieve.isSheafFor_arrows_iff _ _).1 (hsh F)
  have hGsh := (Presieve.isSheafFor_arrows_iff _ _).1 (hsh G)
  obtain ⟨tU, htU, _⟩ := hFsh t hcompat
  refine ⟨tU, ?_⟩
  have hcompatG : Presieve.Arrows.Compatible G.obj f (fun i ↦ G.obj.map (f i).op s) := by
    intro i j Z gi gj hcomp
    simp only
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply, ← op_comp, ← op_comp, hcomp]
  obtain ⟨sU, -, huniq⟩ := hGsh (fun i ↦ G.obj.map (f i).op s) hcompatG
  have hrestr (i : Fin n) : G.obj.map (f i).op (φ.hom.app (op U) tU) =
      G.obj.map (f i).op s := by
    rw [← NatTrans.naturality_apply φ.hom (f i).op tU, htU i, ht i]
  show φ.hom.app (op U) tU = s
  rw [huniq _ hrestr, huniq _ fun _ ↦ rfl]

/-- **The clopen-refinement criterion on the slice site.** Under the hypotheses of
`CategoryTheory.GrothendieckTopology.surjective_sections_of_clopenRefinements`, a locally
surjective morphism of sheaves of types on the slice site `C/U`, in any universe, is surjective
on sections over the final object `U ⟶ U`.

The slice site, with the composite of the forgetful functor and `Q`, satisfies the same
hypotheses at `U ⟶ U`: a covering sieve there is a covering sieve of `U`, whose clopen
decomposition refinement consists of arrows over `U`. -/
theorem surjective_sections_over_of_clopenRefinements (J : GrothendieckTopology C)
    (Q : C ⥤ AlgebraicGeometry.Scheme.{u}) (U : C)
    (hbot : ∀ Z, IsEmpty (Q.obj Z).carrier → (⊥ : Sieve Z) ∈ J Z)
    (hmono : ∀ {X Y : C} (f : X ⟶ Y), Mono (Q.map f) → Mono f)
    (href : ∀ S : Sieve U, S ∈ J U →
      ∃ (n : ℕ) (V : Fin n → C) (f : (i : Fin n) → V i ⟶ U),
        ProetaleWContractible.IsClopenDecompositionCover
          (fun i ↦ Q.obj (V i)) (fun i ↦ Q.map (f i)) ∧
        Sieve.ofArrows V f ∈ J U ∧ ∀ i, S.arrows (f i))
    {F G : Sheaf (J.over U) (Type t)} (φ : F ⟶ G) (hφ : Sheaf.IsLocallySurjective φ) :
    Function.Surjective (φ.hom.app (op (Over.mk (𝟙 U)))) := by
  refine surjective_sections_of_clopenRefinements (J.over U) (Over.forget U ⋙ Q)
    (Over.mk (𝟙 U)) (fun Z hZ ↦ ?_) (fun f hf ↦ ?_) (fun S hS ↦ ?_) F G φ hφ
  · rw [GrothendieckTopology.mem_over_iff, OrderIso.map_bot]
    exact hbot Z.left hZ
  · have : Mono f.left := hmono f.left hf
    exact Over.mono_of_mono_left f
  · obtain ⟨n, V, f, hdec, hcov, hS'⟩ := href _ ((GrothendieckTopology.mem_over_iff _ _).1 hS)
    refine ⟨n, fun i ↦ Over.mk (f i), fun i ↦ Over.homMk (f i) (Category.comp_id _), hdec,
      ?_, fun i ↦ ?_⟩
    · rw [GrothendieckTopology.mem_over_iff, Sieve.overEquiv_ofArrows]
      exact hcov
    · have h := (Sieve.overEquiv_iff S (f i)).1 (hS' i)
      convert h using 2
      simp

/-- An object `U` of a site is weakly contractible as soon as every covering sieve of `U` is
refined by a finite family of morphisms whose images in schemes form a disjoint clopen cover.

This is `CategoryTheory.GrothendieckTopology.surjective_sections_of_clopenRefinements` read at
the morphism universe of the site, which is the universe weak contractibility is stated at. -/
theorem isWeaklyContractible_of_clopenRefinements (J : GrothendieckTopology C)
    (Q : C ⥤ AlgebraicGeometry.Scheme.{u}) (U : C)
    (hbot : ∀ Z, IsEmpty (Q.obj Z).carrier → (⊥ : Sieve Z) ∈ J Z)
    (hmono : ∀ {X Y : C} (f : X ⟶ Y), Mono (Q.map f) → Mono f)
    (href : ∀ S : Sieve U, S ∈ J U →
      ∃ (n : ℕ) (V : Fin n → C) (f : (i : Fin n) → V i ⟶ U),
        ProetaleWContractible.IsClopenDecompositionCover
          (fun i ↦ Q.obj (V i)) (fun i ↦ Q.map (f i)) ∧
        Sieve.ofArrows V f ∈ J U ∧ ∀ i, S.arrows (f i)) :
    J.IsWeaklyContractible U := by
  intro F G φ hφ
  exact surjective_sections_of_clopenRefinements J Q U hbot hmono href F G φ hφ

end CategoryTheory.GrothendieckTopology

namespace ProetaleWContractible

open AlgebraicGeometry

/-- A clopen decomposition cover of `X` transports along an isomorphism `X ≅ Y` to one of `Y`:
the image of each composite is the preimage of the original image under the induced
homeomorphism, so all four conditions are preserved. -/
theorem IsClopenDecompositionCover.comp_iso {X Y : Scheme.{u}} (e : X ≅ Y)
    {n : ℕ} (U : Fin n → Scheme.{u}) (f : (i : Fin n) → U i ⟶ X)
    (h : IsClopenDecompositionCover U f) :
    IsClopenDecompositionCover U (fun i ↦ f i ≫ e.hom) := by
  classical
  let H : X.carrier ≃ₜ Y.carrier := TopCat.homeoOfIso (asIso e.hom.base)
  have hrange (i : Fin n) :
      Set.range (f i ≫ e.hom).base = H.symm ⁻¹' Set.range (f i).base := by
    simpa [Scheme.Hom.comp_base, TopCat.hom_comp, ContinuousMap.coe_comp,
      Set.range_comp, H, TopCat.homeoOfIso] using
      (Homeomorph.image_eq_preimage_symm H (Set.range (f i).base))
  refine ⟨fun i ↦ ?_, fun i ↦ ?_, fun i j hij ↦ ?_, ?_⟩
  · let _ := h.openImmersion i
    infer_instance
  · rw [hrange]
    exact (h.clopen i).preimage H.symm.continuous
  · rw [hrange, hrange]
    exact (h.disjoint i j hij).preimage H.symm
  · rw [Set.iUnion_congr hrange, ← Set.preimage_iUnion, h.cover]
    simp

/-- An affine scheme which is a weakly contractible object of the pro-étale site has
w-contractible ring of global sections.

Weak contractibility is a property of the object, so it transports along the canonical
isomorphism of `T` with the spectrum of its ring of global sections, where Stacks 098H reads
it back as w-contractibility of that ring. -/
theorem isWContractible_of_isWeaklyContractible (T : Scheme.{u}) [IsAffine T]
    (hW : Scheme.proetaleTopology.IsWeaklyContractible T) :
    IsWContractible.{u, u} Γ(T, ⊤) := by
  let e : specOf Γ(T, ⊤) ≅ T := T.isoSpec.symm
  refine ((main_theorem Γ(T, ⊤)).out 2 1).mp fun F G φ hφ s ↦ ?_
  obtain ⟨t, ht⟩ := hW F G φ hφ (G.obj.map e.inv.op s)
  have ht' : φ.hom.app (op T) t = G.obj.map e.inv.op s := by simpa using ht
  refine ⟨F.obj.map e.hom.op t, ?_⟩
  calc φ.hom.app (op (specOf Γ(T, ⊤))) (F.obj.map e.hom.op t)
        = G.obj.map e.hom.op (φ.hom.app (op T) t) := by simp
    _ = s := by
        rw [ht']
        show (G.obj.map e.inv.op ≫ G.obj.map e.hom.op) s = s
        rw [← Functor.map_comp]
        simp

end ProetaleWContractible

namespace AlgebraicGeometry.ProEtale

open ProetaleWContractible

/-- **Stacks 098H, (1) implies (3).** Let `T` be an affine object of a chosen big pro-étale
site whose ring of global sections is w-contractible. Then every covering sieve of `T` is
refined by a finite family of objects of the site whose images form a disjoint clopen cover of
`T`.

The refinement is produced for the spectrum of the ring of global sections by Stacks 098F and
transported along the canonical isomorphism with `T`; its members are open subschemes of `T`
and therefore satisfy the size cutoff of the site. -/
theorem exists_clopenRefinement_of_isWContractible (B : BigProetaleSite.{u}) (T : B.Scheme)
    [IsAffine T.obj] (hW : IsWContractible.{u, u} Γ(T.obj, ⊤))
    (S : Sieve T) (hS : S ∈ B.topology T) :
    ∃ (n : ℕ) (U : Fin n → B.Scheme) (f : (i : Fin n) → U i ⟶ T),
      IsClopenDecompositionCover (fun i ↦ (U i).obj) (fun i ↦ B.inclusion.map (f i)) ∧
      ∀ i, S.arrows (f i) := by
  classical
  let e : specOf Γ(T.obj, ⊤) ≅ T.obj := T.obj.isoSpec.symm
  obtain ⟨E, hE, hES⟩ := (B.mem_topology_iff S).mp hS
  have hAmb : Sieve.generate (E.map B.inclusion).presieve₀ ∈
      Scheme.proetaleTopology T.obj :=
    Precoverage.generate_mem_toGrothendieck ((B.isProetaleCovering_iff ⟨T, E⟩).mp hE.1)
  obtain ⟨n, V, g, hdec, href⟩ :=
    everyProetaleCoverHasZariskiRefinement_of_wContractible Γ(T.obj, ⊤) hW
      ((Sieve.generate (E.map B.inclusion).presieve₀).pullback e.hom)
      (Scheme.proetaleTopology.pullback_stable e.hom hAmb)
  have hdecT := IsClopenDecompositionCover.comp_iso e V g hdec
  have hsize (i : Fin n) : (V i).size < B.cutoff := by
    have : IsOpenImmersion (g i ≫ e.hom) := hdecT.openImmersion i
    exact Scheme.size_lt_of_isOpenImmersion (g i ≫ e.hom) T.property
  let U : Fin n → B.Scheme := fun i ↦ ⟨V i, hsize i⟩
  let f : (i : Fin n) → U i ⟶ T := fun i ↦ B.inclusion.preimage
    (show B.inclusion.obj (U i) ⟶ B.inclusion.obj T from g i ≫ e.hom)
  have hmapf (i : Fin n) : B.inclusion.map (f i) = g i ≫ e.hom :=
    B.inclusion.map_preimage (show B.inclusion.obj (U i) ⟶ B.inclusion.obj T from g i ≫ e.hom)
  refine ⟨n, U, f, by simpa only [show (fun i ↦ (U i).obj) = V from rfl, hmapf] using hdecT,
    fun i ↦ ?_⟩
  have hi : (Sieve.generate (E.map B.inclusion).presieve₀).arrows (g i ≫ e.hom) := href i
  rw [Sieve.generate_apply] at hi
  obtain ⟨Y, a, b, hb, hab⟩ := hi
  change Presieve.ofArrows (fun j ↦ (E.X j).obj) (fun j ↦ B.inclusion.map (E.f j)) b at hb
  obtain ⟨j⟩ := hb
  let a' : U i ⟶ E.X j :=
    B.inclusion.preimage (show B.inclusion.obj (U i) ⟶ B.inclusion.obj (E.X j) from a)
  have hfac : a' ≫ E.f j = f i := by
    apply B.inclusion.map_injective
    rw [Functor.map_comp, B.inclusion.map_preimage, hmapf]
    simpa [a', Category.assoc] using hab
  rw [← hfac]
  exact S.downward_closed (hES _ _ (E.presieve₀_f j)) a'

/-- A zero-hypercover of an object of a chosen big pro-étale site whose image in schemes is a
pro-étale covering generates a covering sieve. -/
private theorem generate_presieve₀_mem_topology (B : BigProetaleSite.{u}) {T : B.Scheme}
    (E : PreZeroHypercover.{u + 1} T)
    (h : (E.map B.inclusion).presieve₀ ∈ Scheme.proetalePrecoverage.coverings T.obj) :
    Sieve.generate E.presieve₀ ∈ B.topology T := by
  refine Precoverage.generate_mem_toGrothendieck ?_
  rw [B.precoverage_eq_comap, Precoverage.mem_comap_iff, ← PreZeroHypercover.presieve₀_map]
  exact h

/-- A sieve on an object of a chosen big pro-étale site whose underlying scheme has empty space
is covering, the empty family being a pro-étale covering of such a scheme. -/
theorem BigProetaleSite.bot_mem_topology_of_isEmpty (B : BigProetaleSite.{u}) (Z : B.Scheme)
    (hZ : IsEmpty (B.inclusion.obj Z).carrier) :
    (⊥ : Sieve Z) ∈ B.topology Z := by
  let _ : IsEmpty (B.inclusion.obj Z).carrier := hZ
  rw [← Sieve.generate_bot]
  refine Precoverage.generate_mem_toGrothendieck ?_
  show (⊥ : Presieve Z) ∈ B.precoverage.coverings Z
  rw [B.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_bot]
  exact Scheme.bot_mem_propQCPrecoverage (P := @WeaklyEtale) (B.inclusion.obj Z)

/-- A finite family of morphisms of a chosen big pro-étale site whose images form a disjoint
clopen cover of the target generates a covering sieve: the family is a Zariski covering of the
underlying scheme, hence a pro-étale one. -/
theorem BigProetaleSite.sieve_ofArrows_mem_topology_of_isClopenDecompositionCover
    (B : BigProetaleSite.{u}) (T : B.Scheme) {n : ℕ} (U : Fin n → B.Scheme)
    (f : (i : Fin n) → U i ⟶ T)
    (hdec : IsClopenDecompositionCover (fun i ↦ (U i).obj) (fun i ↦ B.inclusion.map (f i))) :
    Sieve.ofArrows U f ∈ B.topology T := by
  classical
  let E : PreZeroHypercover.{u + 1} T :=
    { I₀ := ULift.{u + 1} (Fin n)
      X i := U i.down
      f i := f i.down }
  let _ : MorphismProperty.ContainsIdentities @WeaklyEtale := ⟨fun _ ↦ inferInstance⟩
  have hZ : (E.map B.inclusion).presieve₀ ∈ Scheme.zariskiPrecoverage T.obj := by
    rw [Scheme.presieve₀_mem_precoverage_iff]
    refine ⟨fun x ↦ ?_, fun i ↦ hdec.openImmersion i.down⟩
    have hx : x ∈ ⋃ i, Set.range (B.inclusion.map (f i)).base :=
      (Set.ext_iff.mp hdec.cover x).mpr (Set.mem_univ x)
    obtain ⟨i, y, hy⟩ := Set.mem_iUnion.mp hx
    exact ⟨ULift.up i, y, hy⟩
  have hle : Scheme.zariskiPrecoverage ≤ Scheme.propQCPrecoverage @WeaklyEtale :=
    Scheme.zariskiPrecoverage_le_propQCPrecoverage
  have heq : E.presieve₀ = Presieve.ofArrows U f := by
    funext Y g
    exact propext ⟨fun ⟨i⟩ ↦ ⟨i.down⟩, fun ⟨i⟩ ↦ ⟨ULift.up i⟩⟩
  show Sieve.generate (Presieve.ofArrows U f) ∈ B.topology T
  rw [← heq]
  exact generate_presieve₀_mem_topology B E (hle T.obj hZ)

/-- **Stacks 098H, (3) implies (2).** An object of a chosen big pro-étale site each of whose
covering sieves is refined by a finite family whose images form a disjoint clopen cover is a
weakly contractible object of the site. -/
theorem BigProetaleSite.isWeaklyContractible_of_clopenRefinements (B : BigProetaleSite.{u})
    (T : B.Scheme)
    (h3 : ∀ S : Sieve T, S ∈ B.topology T →
      ∃ (n : ℕ) (U : Fin n → B.Scheme) (f : (i : Fin n) → U i ⟶ T),
        IsClopenDecompositionCover (fun i ↦ (U i).obj) (fun i ↦ B.inclusion.map (f i)) ∧
        ∀ i, S.arrows (f i)) :
    B.topology.IsWeaklyContractible T := by
  refine GrothendieckTopology.isWeaklyContractible_of_clopenRefinements B.topology B.inclusion T
    B.bot_mem_topology_of_isEmpty (fun f hf ↦ B.inclusion.mono_of_mono_map hf) ?_
  intro S hS
  obtain ⟨n, U, f, hdec, href⟩ := h3 S hS
  exact ⟨n, U, f, hdec,
    B.sieve_ofArrows_mem_topology_of_isClopenDecompositionCover T U f hdec, href⟩

/-- **Stacks 098H, (2) implies (1).** A weakly contractible affine object of a chosen big
pro-étale site has w-contractible ring of global sections.

The site contains the spectrum of a faithfully flat ind-étale w-contractible extension `D` of
the ring of global sections `A` (Stacks 0984, whose cardinality bound is the one the cutoff of
the site is closed under). The topology being subcanonical, that one-element covering is a
surjection of sheaves, which weak contractibility splits into a retraction of `A → D`. For a
faithfully flat weakly étale `A → C` the base change `D → D ⊗_A C` is again one, so it is split
by w-contractibility of `D`, and the two retractions compose to one of `A → C`. -/
theorem BigProetaleSite.isWContractible_of_isWeaklyContractible (B : BigProetaleSite.{u})
    (T : B.Scheme) [IsAffine T.obj] (h2 : B.topology.IsWeaklyContractible T) :
    IsWContractible.{u, u} Γ(T.obj, ⊤) := by
  classical
  let A := Γ(T.obj, ⊤)
  let κ := T.obj.size
  have hκ : Cardinal.aleph0 ≤ κ := by
    show Cardinal.aleph0 ≤ T.obj.size
    rw [Scheme.size_of_isAffine T.obj]
    exact le_max_left _ _
  have hA : Cardinal.mk A ≤ κ := by
    show Cardinal.mk Γ(T.obj, ⊤) ≤ T.obj.size
    rw [Scheme.size_of_isAffine T.obj]
    exact le_max_right _ _
  obtain ⟨D, hD, f₀, hff, hind, hwd, hDmk⟩ :=
    exists_small_faithfullyFlat_ind_etale_wContractible A κ hκ hA
  let _ : CommRing D := hD
  let _ : Algebra A D := f₀.toAlgebra
  have hRingInd : CommRingCat.etale.ind (CommRingCat.ofHom f₀) := by
    rw [MorphismProperty.ind_iff_ind_underMk]
    exact hind
  have hindAlg : (CommAlgCat.etale A).ind (CommAlgCat.of A D) := by
    rw [CommAlgCat.ind_etale_iff_ind_algebraMap]
    simpa using hRingInd
  have hweak : Algebra.WeaklyEtale A D := Algebra.weaklyEtale_of_ind_etale
    (StacksDraft.indEtale_iff.mpr hindAlg)
  have hwe : IsWeaklyEtale A D := (Algebra.weaklyEtale_iff A D).mp hweak
  have hDsize : (Spec (CommRingCat.of D)).size ≤ Cardinal.proetaleBound κ := by
    rw [Scheme.size_Spec]
    refine max_le ?_ (hDmk.trans (le_max_left _ _))
    exact hκ.trans ((Cardinal.self_le_power κ Cardinal.one_le_aleph0).trans
      ((le_max_left _ _).trans (le_max_right _ _)))
  let V : B.Scheme := ⟨Spec (CommRingCat.of D), B.closed_under_proetaleBound T.property hDsize⟩
  let e : Spec A ≅ T.obj := T.obj.isoSpec.symm
  let r : A ⟶ CommRingCat.of D := CommRingCat.ofHom (algebraMap A D)
  let g₀ : V.obj ⟶ T.obj := Spec.map r ≫ e.hom
  let g : V ⟶ T := B.inclusion.preimage g₀
  have hg : B.inclusion.map g = g₀ := B.inclusion.map_preimage _
  have hffr : r.hom.FaithfullyFlat := RingHom.faithfullyFlat_algebraMap_iff.mpr hff
  have hflat : Flat (Spec.map r) := ((flat_and_surjective_SpecMap_iff r).mpr hffr).1
  have hsurjr : Surjective (Spec.map r) := ((flat_and_surjective_SpecMap_iff r).mpr hffr).2
  have hdiag : Flat (pullback.diagonal (Spec.map r)) := by
    show Flat (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap A D))))
    rw [diagonal_SpecMap A D]
    have hm : Flat (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lmul' A (S := D)).toRingHom)) := by
      rw [HasRingHomProperty.Spec_iff (P := @Flat)]
      exact hwe.2
    exact MorphismProperty.comp_mem _ _ _ hm inferInstance
  have hwer : WeaklyEtale (Spec.map r) := ⟨hflat, hdiag⟩
  have hweg : WeaklyEtale g₀ := by
    show WeaklyEtale (Spec.map r ≫ e.hom); infer_instance
  have hsurjg : Surjective g₀ := by
    show Surjective (Spec.map r ≫ e.hom); infer_instance
  have hqcg : QuasiCompact g₀ := quasiCompact_of_compactSpace _
  have hsing : Presieve.singleton g₀ ∈ Scheme.proetalePrecoverage.coverings T.obj :=
    Scheme.Hom.singleton_mem_propQCPrecoverage hweg
  let I : Type (u + 1) := ULift.{u + 1} Unit
  let E : PreZeroHypercover.{u + 1} T :=
    { I₀ := I
      X _ := V
      f _ := g }
  have hcover : Sieve.ofArrows (fun _ : I ↦ V) (fun _ ↦ g) ∈ B.topology T := by
    refine generate_presieve₀_mem_topology B E ?_
    show Presieve.ofArrows (fun _ : I ↦ B.inclusion.obj V) (fun _ ↦ B.inclusion.map g) ∈
      Scheme.proetalePrecoverage.coverings (B.inclusion.obj T)
    rw [hg, Presieve.ofArrows_of_unique]
    exact hsing
  let J := B.topology
  let φ : J.yoneda.obj V ⟶ J.yoneda.obj T := J.yoneda.map g
  have hpsh : (sheafToPresheaf J (Type u)).map φ = yoneda.map g := J.yoneda_map_hom g
  have hls : Sheaf.IsLocallySurjective φ := by
    rw [← Sheaf.isLocallySurjective_sheafToPresheaf_map_iff, hpsh]
    let ι := ULift.{u} Unit
    let _ : Presheaf.IsLocallySurjective J (coprodYonedaDesc (fun _ : ι ↦ V) T (fun _ ↦ g)) :=
      isLocallySurjective_coprodYonedaDesc J (fun _ : ι ↦ V) T (fun _ ↦ g)
        (by simpa only [Sieve.ofArrows, Presieve.ofArrows_of_unique] using hcover)
    exact Presheaf.isLocallySurjective_of_isLocallySurjective_fac J
      (show Sigma.desc (fun _ : ι ↦ 𝟙 (yoneda.obj V)) ≫ yoneda.map g =
        coprodYonedaDesc (fun _ : ι ↦ V) T (fun _ ↦ g) from by
        ext i; simp [coprodYonedaDesc])
  obtain ⟨s, hs⟩ := h2 (J.yoneda.obj V) (J.yoneda.obj T) φ hls (𝟙 T)
  have hs' : s ≫ g = 𝟙 T := by
    have happ : (yoneda.map g).app (op T) s = s ≫ g := by
      simp only [yoneda_map_app]; rfl
    rw [hpsh, happ] at hs
    exact hs
  have hsAmb : B.inclusion.map s ≫ Spec.map r ≫ e.hom = 𝟙 T.obj := by
    have hmap := congrArg B.inclusion.map hs'
    rw [Functor.map_comp, hg] at hmap
    simpa [g₀, Category.assoc] using hmap
  have hs0 : (e.hom ≫ B.inclusion.map s) ≫ Spec.map r = 𝟙 _ := by
    apply (cancel_mono e.hom).1
    simpa only [Category.assoc, Category.id_comp, Category.comp_id] using
      congrArg (fun q ↦ e.hom ≫ q) hsAmb
  have hret : HasRetraction A D := hasRetraction_of_section A D (e.hom ≫ B.inclusion.map s) hs0
  intro C _ _ hweC hffC
  let E' := TensorProduct A D C
  let _ : Algebra.WeaklyEtale A C := (Algebra.weaklyEtale_iff A C).mpr hweC
  let _ : Algebra D E' := inferInstance
  let _ : IsScalarTower A D E' := inferInstance
  let _ : Algebra.WeaklyEtale D E' := inferInstance
  let _ : Module.FaithfullyFlat D E' := inferInstance
  obtain ⟨σ⟩ := hwd E' ((Algebra.weaklyEtale_iff D E').mp inferInstance) inferInstance
  obtain ⟨τ⟩ := hret
  exact ⟨τ.comp ((σ.restrictScalars A).comp
    (Algebra.TensorProduct.includeRight (R := A) (A := D) (B := C)))⟩

/-- **Stacks 098H.** For an affine object `T` of a chosen big pro-étale site the following are
equivalent: the ring of global sections of `T` is w-contractible; `T` is a weakly contractible
object of the site; every covering sieve of `T` is refined by a finite family of objects of the
site whose images form a disjoint clopen cover of `T`. -/
@[stacks 098H]
theorem isWContractible_globalSections_tfae (B : BigProetaleSite.{u}) (T : B.Scheme)
    [IsAffine T.obj] :
    [IsWContractible.{u, u} Γ(T.obj, ⊤),
      B.topology.IsWeaklyContractible T,
      ∀ S : Sieve T, S ∈ B.topology T →
        ∃ (n : ℕ) (U : Fin n → B.Scheme) (f : (i : Fin n) → U i ⟶ T),
          IsClopenDecompositionCover (fun i ↦ (U i).obj) (fun i ↦ B.inclusion.map (f i)) ∧
          ∀ i, S.arrows (f i)].TFAE := by
  tfae_have h13 : 1 → 3 := fun hW S hS ↦
    exists_clopenRefinement_of_isWContractible B T hW S hS
  tfae_have h32 : 3 → 2 := fun h3 ↦ B.isWeaklyContractible_of_clopenRefinements T h3
  tfae_have h21 : 2 → 1 := fun h2 ↦ B.isWContractible_of_isWeaklyContractible T h2
  tfae_finish

end AlgebraicGeometry.ProEtale

end
