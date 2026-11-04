module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.Groupoids.More.FinitePart.Presheaf
public import StacksFrontier.AlgebraicGeometry.Spaces.ImmersionBaseChange
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallZariskiSite
public import StacksFrontier.AlgebraicGeometry.Spaces.SubspacePreimage

/-!
# The finite part of an open immersion over the base

Fix a commutative triangle `X' --j--> X` over `Y` of algebraic spaces over a scheme `S` with `j`
an open immersion. Then the finite part of `X' ⟶ Y` maps canonically and injectively into the
finite part of `X ⟶ Y`: a pair consisting of a morphism `a : T ⟶ Y` and an open subspace of
`T ×_Y X'` finite over `T` is sent to the pair with the same `a` and the image of that open
subspace in `T ×_Y X`.

## Main definitions

* `AlgebraicGeometry.Space.finiteOpenSubspaceMap` — Stacks 04PF: the canonical monomorphism
  `(X'/Y)_fin ⟶ (X/Y)_fin`, together with its description on finite open pairs.

## Implementation notes

The map is returned as an element of a subtype: the natural transformation bundled with the
proof that it is a monomorphism and with its per-test-scheme description. The description is
what pins it down — on a pair `(a, Z')` the image pair has the same morphism to `Y`, and its
open subspace is isomorphic to `Z'` compatibly with both projections, the second twisted by
`j`. Returning the data and its specification together avoids a second declaration whose
agreement with the construction would have to be asserted separately.

The image is formed as `CategoryTheory.Subfunctor.range` of the composite of the inclusion of
`Z'` with the comparison morphism `T ×_Y X' ⟶ T ×_Y X`. That comparison is an open immersion,
being a base change of `j`, so the composite is an open immersion and in particular a
monomorphism, which is what makes the range an open subspace isomorphic to `Z'`; finiteness
over `T` transports along that isomorphism.

Naturality is the statement that the image of a base change is a base change of the image,
together with uniqueness of base changes of a fixed pair along a fixed morphism.

## References

* [Stacks Project, Tag 04PF](https://stacks.math.columbia.edu/tag/04PF)
* [Stacks Project, Tag 04PC](https://stacks.math.columbia.edu/tag/04PC)
* [Stacks Project, Tag 04PD](https://stacks.math.columbia.edu/tag/04PD)
-/

public section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

private noncomputable def finiteOpenAmbientMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T X' X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (a : T ⟶ Y) (j : X' ⟶ X) (f' : X' ⟶ Y) (f : X ⟶ Y)
    (hj : j ≫ f = f') :
    pullback a.hom f'.hom ⟶ pullback a.hom f.hom :=
  pullback.map a.hom f'.hom a.hom f.hom (𝟙 _) j.hom (𝟙 _) (by simp)
    (by simpa using congrArg (fun g : X' ⟶ Y => g.hom) hj.symm)

private theorem finiteOpenAmbientMap_fst
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T X' X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (a : T ⟶ Y) (j : X' ⟶ X) (f' : X' ⟶ Y) (f : X ⟶ Y)
    (hj : j ≫ f = f') :
    finiteOpenAmbientMap B S hS a j f' f hj ≫ pullback.fst a.hom f.hom =
      pullback.fst a.hom f'.hom := by
  simp only [finiteOpenAmbientMap, pullback.map, Category.comp_id,
    pullback.lift_fst]

private theorem finiteOpenAmbientMap_snd
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T X' X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (a : T ⟶ Y) (j : X' ⟶ X) (f' : X' ⟶ Y) (f : X ⟶ Y)
    (hj : j ≫ f = f') :
    finiteOpenAmbientMap B S hS a j f' f hj ≫ pullback.snd a.hom f.hom =
      pullback.snd a.hom f'.hom ≫ j.hom := by
  simp only [finiteOpenAmbientMap, pullback.map, Category.comp_id,
    pullback.lift_snd]

private theorem mono_of_openImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (f : F ⟶ G) (hf : AlgebraicGeometry.Space.IsOpenImmersion B S hS f) : Mono f := by
  let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
    MorphismProperty Scheme.{u}) (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  have hQmono : Q ≤ MorphismProperty.monomorphisms
      (AlgebraicGeometry.BigFppfOver B S hS) := by
    intro A A' a ha
    have hmono : Mono ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map a) :=
      AlgebraicGeometry.IsOpenImmersion.le_monomorphisms _ ha
    refine ⟨fun {T} b c hbc => ?_⟩
    apply Functor.map_injective (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
    apply (cancel_mono ((AlgebraicGeometry.BigFppfOver.toScheme B S hS).map a)).1
    exact congrArg (fun k => (AlgebraicGeometry.BigFppfOver.toScheme B S hS).map k) hbc
  exact MorphismProperty.presheaf_monomorphisms_le_monomorphisms _
    (MorphismProperty.relative_monotone hQmono _ hf)

private theorem isAlgebraicSpace_of_iso_symm
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : F ≅ G) (hG : AlgebraicGeometry.IsAlgebraicSpace B S hS G) :
    AlgebraicGeometry.IsAlgebraicSpace B S hS F := by
  refine ⟨(Presheaf.isSheaf_of_iso_iff
    (J := AlgebraicGeometry.BigFppfOver.topology B S hS) e).mpr hG.isSheaf, ?_, ?_⟩
  · exact (MorphismProperty.cancel_right_of_respectsIso
      (P := yoneda.relativelyRepresentable) (diag F) (prod.map e.hom e.hom)).mp
        (by simpa only [prod.diag_map] using
          ((MorphismProperty.cancel_left_of_respectsIso
            (P := yoneda.relativelyRepresentable) e.hom (diag G)).mpr
            hG.diagonal_representable))
  · obtain ⟨U, a, haSurj, haEtale⟩ := hG.exists_atlas
    exact ⟨U, a ≫ e.inv,
      MorphismProperty.RespectsIso.postcomp _ e.inv a haSurj,
      MorphismProperty.RespectsIso.postcomp _ e.inv a haEtale⟩

private theorem isFinite_of_iso_source
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {P Q Z : (AlgebraicGeometry.BigFppfOver B S hS)ᵒᵖ ⥤ Type u}
    (e : P ≅ Q) (f : P ⟶ Z) (g : Q ⟶ Z)
    (he : e.hom ≫ g = f)
    (hf : AlgebraicGeometry.Space.IsFinite B S hS f) :
    AlgebraicGeometry.Space.IsFinite B S hS g := by
  intro A hA ξ
  obtain ⟨A', p, i, hA', hp, hpb⟩ := hf A hA ξ
  exact ⟨A', p, i ≫ e.hom, hA', hp, hpb.of_iso (Iso.refl _) e (Iso.refl _) (Iso.refl _)
    (by simp) (by simp) (by simpa using he.symm) (by simp)⟩

private theorem finiteOpenAmbientMap_isPullback
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T X' X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (a : T ⟶ Y) (j : X' ⟶ X) (f' : X' ⟶ Y) (f : X ⟶ Y)
    (hj : j ≫ f = f') :
    IsPullback (finiteOpenAmbientMap B S hS a j f' f hj)
      (pullback.snd a.hom f'.hom) (pullback.snd a.hom f.hom) j.hom := by
  have houter : IsPullback
      (finiteOpenAmbientMap B S hS a j f' f hj ≫ pullback.fst a.hom f.hom)
      (pullback.snd a.hom f'.hom) a.hom (j.hom ≫ f.hom) := by
    rw [finiteOpenAmbientMap_fst,
      show j.hom ≫ f.hom = f'.hom from congrArg (fun g => g.hom) hj]
    exact IsPullback.of_hasPullback a.hom f'.hom
  exact houter.of_right (finiteOpenAmbientMap_snd B S hS a j f' f hj)
    (IsPullback.of_hasPullback a.hom f.hom)

private theorem finiteOpenAmbientMap_isOpenImmersion
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {T X' X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (a : T ⟶ Y) (j : X' ⟶ X) (f' : X' ⟶ Y) (f : X ⟶ Y)
    (hj : j ≫ f = f') (hjOpen : AlgebraicGeometry.Space.IsOpenImmersion B S hS j.hom) :
    AlgebraicGeometry.Space.IsOpenImmersion B S hS
      (finiteOpenAmbientMap B S hS a j f' f hj) := by
  let M' := AlgebraicGeometry.AlgebraicSpaces.fiberProduct B S hS a f'
  let M := AlgebraicGeometry.AlgebraicSpaces.fiberProduct B S hS a f
  let g : M' ⟶ M := ObjectProperty.homMk
    (finiteOpenAmbientMap B S hS a j f' f hj)
  let s' : M' ⟶ X' := ObjectProperty.homMk (pullback.snd a.hom f'.hom)
  let s : M ⟶ X := ObjectProperty.homMk (pullback.snd a.hom f.hom)
  have hpb : IsPullback g s' s j := by
    apply IsPullback.of_map (ObjectProperty.ι _)
    · exact ObjectProperty.hom_ext _
        (finiteOpenAmbientMap_snd B S hS a j f' f hj)
    · simpa [g, s', s, M', M, AlgebraicGeometry.AlgebraicSpaces.fiberProduct] using
        finiteOpenAmbientMap_isPullback B S hS a j f' f hj
  exact AlgebraicGeometry.Space.isOpenImmersion_of_isPullback B S hS hpb.flip hjOpen

private theorem isOpenImmersion_ι_comp_finiteOpenAmbientMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (j : X' ⟶ X) (f' : X' ⟶ Y) (f : X ⟶ Y) (hj : j ≫ f = f')
    (hjOpen : AlgebraicGeometry.Space.IsOpenImmersion B S hS j.hom)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (p : AlgebraicGeometry.Space.FiniteOpenSubspace B S hS f'
      (AlgebraicGeometry.schemeSpace T)) :
    AlgebraicGeometry.Space.IsOpenImmersion B S hS
      (p.subspace.ι ≫ finiteOpenAmbientMap B S hS p.toBase j f' f hj) := by
  let Q := MorphismProperty.inverseImage (@AlgebraicGeometry.IsOpenImmersion.{u} :
    MorphismProperty Scheme.{u}) (AlgebraicGeometry.BigFppfOver.toScheme B S hS)
  show Q.presheaf _
  exact MorphismProperty.comp_mem Q.presheaf _ _ p.isOpen.2
    (finiteOpenAmbientMap_isOpenImmersion B S hS p.toBase j f' f hj hjOpen)

/-- Composing the inclusion of a range with a map to the target of `u ≫ g` factors through `u`. -/
private theorem toRange_ι_comp_comp {C : Type*} [Category C] {F G H K : C ⥤ Type u}
    (u : F ⟶ G) (g : G ⟶ H) (c : H ⟶ K) (d : G ⟶ K) (h : g ≫ c = d) :
    (Subfunctor.toRange (u ≫ g) ≫ (Subfunctor.range (u ≫ g)).ι) ≫ c = u ≫ d := by
  rw [Subfunctor.toRange_ι, Category.assoc, h]

private noncomputable def finiteOpenImagePair
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    {X' X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (j : X' ⟶ X) (f' : X' ⟶ Y) (f : X ⟶ Y) (hj : j ≫ f = f')
    (hjOpen : AlgebraicGeometry.Space.IsOpenImmersion B S hS j.hom)
    (p : AlgebraicGeometry.Space.FiniteOpenSubspace B S hS f'
      (AlgebraicGeometry.schemeSpace T)) :
    AlgebraicGeometry.Space.FiniteOpenSubspace B S hS f
      (AlgebraicGeometry.schemeSpace T) := by
  classical
  let M' := AlgebraicGeometry.AlgebraicSpaces.fiberProduct B S hS p.toBase f'
  let M := AlgebraicGeometry.AlgebraicSpaces.fiberProduct B S hS p.toBase f
  let g : M' ⟶ M := ObjectProperty.homMk
    (finiteOpenAmbientMap B S hS p.toBase j f' f hj)
  let r : p.subspace.toFunctor ⟶ M.1 := p.subspace.ι ≫ g.hom
  have hrOpen : AlgebraicGeometry.Space.IsOpenImmersion B S hS r :=
    isOpenImmersion_ι_comp_finiteOpenAmbientMap B S hS j f' f hj hjOpen T p
  have : Mono r := mono_of_openImmersion B S hS r hrOpen
  let Z : Subfunctor M.1 := Subfunctor.range r
  let e : p.subspace.toFunctor ≅ Z.toFunctor := asIso (Subfunctor.toRange r)
  have hZ : AlgebraicGeometry.Space.IsOpenSubspace B S hS Z :=
    isOpenSubspace_range_of_open B S hS r p.isOpen.1 hrOpen
  have hproj : e.hom ≫ (Z.ι ≫ pullback.fst p.toBase.hom f.hom) =
      p.subspace.ι ≫ pullback.fst p.toBase.hom f'.hom := by
    exact toRange_ι_comp_comp _ _ _ _ (finiteOpenAmbientMap_fst B S hS p.toBase j f' f hj)
  have hfinite : AlgebraicGeometry.Space.IsFinite B S hS
      (Z.ι ≫ pullback.fst p.toBase.hom f.hom) :=
    isFinite_of_iso_source B S hS e
      (p.subspace.ι ≫ pullback.fst p.toBase.hom f'.hom)
      (Z.ι ≫ pullback.fst p.toBase.hom f.hom) hproj p.finite_projection
  exact ⟨p.toBase, Z, hZ, hfinite⟩

private theorem finiteOpenImagePair_iso
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (j : X' ⟶ X) (f' : X' ⟶ Y) (f : X ⟶ Y)
    (hj : j ≫ f = f') (hjOpen : AlgebraicGeometry.Space.IsOpenImmersion B S hS j.hom)
    (T : AlgebraicGeometry.BigFppfOver B S hS)
    (p : AlgebraicGeometry.Space.FiniteOpenSubspace B S hS f'
      (AlgebraicGeometry.schemeSpace T)) :
    ∃ e : p.subspace.toFunctor ≅
        (finiteOpenImagePair B S hS T j f' f hj hjOpen p).subspace.toFunctor,
      e.hom ≫ (finiteOpenImagePair B S hS T j f' f hj hjOpen p).subspace.ι ≫
          pullback.fst p.toBase.hom f.hom =
        p.subspace.ι ≫ pullback.fst p.toBase.hom f'.hom ∧
      e.hom ≫ (finiteOpenImagePair B S hS T j f' f hj hjOpen p).subspace.ι ≫
          pullback.snd p.toBase.hom f.hom =
        p.subspace.ι ≫ pullback.snd p.toBase.hom f'.hom ≫ j.hom := by
  classical
  let g : pullback p.toBase.hom f'.hom ⟶ pullback p.toBase.hom f.hom :=
    finiteOpenAmbientMap B S hS p.toBase j f' f hj
  let r : p.subspace.toFunctor ⟶ pullback p.toBase.hom f.hom := p.subspace.ι ≫ g
  let Z : Subfunctor (pullback p.toBase.hom f.hom) := Subfunctor.range r
  have : Mono r := mono_of_openImmersion B S hS r
    (isOpenImmersion_ι_comp_finiteOpenAmbientMap B S hS j f' f hj hjOpen T p)
  let e : p.subspace.toFunctor ≅ Z.toFunctor := asIso (Subfunctor.toRange r)
  refine ⟨e, ?_, ?_⟩
  · exact toRange_ι_comp_comp _ _ _ _ (finiteOpenAmbientMap_fst B S hS p.toBase j f' f hj)
  · exact toRange_ι_comp_comp _ _ _ _ (finiteOpenAmbientMap_snd B S hS p.toBase j f' f hj)

private theorem finiteOpenImagePair_isBaseChange
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (j : X' ⟶ X) (f' : X' ⟶ Y) (f : X ⟶ Y)
    (hj : j ≫ f = f') (hjOpen : AlgebraicGeometry.Space.IsOpenImmersion B S hS j.hom)
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (h : T' ⟶ T)
    (p : AlgebraicGeometry.Space.FiniteOpenSubspace B S hS f'
      (AlgebraicGeometry.schemeSpace T))
    (q : AlgebraicGeometry.Space.FiniteOpenSubspace B S hS f'
      (AlgebraicGeometry.schemeSpace T'))
    (H : AlgebraicGeometry.Space.FiniteOpenSubspace.IsBaseChange B S hS f' h p q) :
    AlgebraicGeometry.Space.FiniteOpenSubspace.IsBaseChange B S hS f h
      (finiteOpenImagePair B S hS T j f' f hj hjOpen p)
      (finiteOpenImagePair B S hS T' j f' f hj hjOpen q) := by
  obtain ⟨hbase, k, hpb, hX⟩ := H
  obtain ⟨eP, hPfst, hPsnd⟩ := finiteOpenImagePair_iso B S hS j f' f hj hjOpen T p
  obtain ⟨eQ, hQfst, hQsnd⟩ := finiteOpenImagePair_iso B S hS j f' f hj hjOpen T' q
  let k' := eQ.inv ≫ k ≫ eP.hom
  have hpb' : IsPullback
      ((finiteOpenImagePair B S hS T' j f' f hj hjOpen q).subspace.ι ≫
        pullback.fst q.toBase.hom f.hom)
      k' (yoneda.map h)
      ((finiteOpenImagePair B S hS T j f' f hj hjOpen p).subspace.ι ≫
        pullback.fst p.toBase.hom f.hom) := by
    apply hpb.of_iso eQ (Iso.refl _) eP (Iso.refl _)
    · simpa [k', Category.assoc, AlgebraicGeometry.schemeSpace] using hQfst.symm
    · simp [k']
    · rfl
    · simpa [k', Category.assoc, AlgebraicGeometry.schemeSpace] using hPfst.symm
  have hX' : k' ≫
      (finiteOpenImagePair B S hS T j f' f hj hjOpen p).subspace.ι ≫
        pullback.snd p.toBase.hom f.hom =
      (finiteOpenImagePair B S hS T' j f' f hj hjOpen q).subspace.ι ≫
        pullback.snd q.toBase.hom f.hom := by
    dsimp [k']
    calc
      (eQ.inv ≫ k ≫ eP.hom) ≫
          (finiteOpenImagePair B S hS T j f' f hj hjOpen p).subspace.ι ≫
            pullback.snd p.toBase.hom f.hom =
        eQ.inv ≫ (k ≫ p.subspace.ι ≫ pullback.snd p.toBase.hom f'.hom ≫ j.hom) := by
          simpa only [Category.assoc] using
            congrArg (fun t => eQ.inv ≫ k ≫ t) hPsnd
      _ = eQ.inv ≫ (q.subspace.ι ≫ pullback.snd q.toBase.hom f'.hom ≫ j.hom) :=
          congrArg (fun z => eQ.inv ≫ (z ≫ j.hom)) hX
      _ = (finiteOpenImagePair B S hS T' j f' f hj hjOpen q).subspace.ι ≫
            pullback.snd q.toBase.hom f.hom := by
          rw [← hQsnd]
          simp
  exact ⟨hbase, k', hpb', hX'⟩

private theorem finiteOpenSubspace_eq_of_isBaseChange
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X Y : AlgebraicGeometry.AlgebraicSpaces B S hS} (f : X ⟶ Y)
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (h : T' ⟶ T)
    (p : AlgebraicGeometry.Space.FiniteOpenSubspace B S hS f
      (AlgebraicGeometry.schemeSpace T))
    (q r : AlgebraicGeometry.Space.FiniteOpenSubspace B S hS f
      (AlgebraicGeometry.schemeSpace T'))
    (Hq : AlgebraicGeometry.Space.FiniteOpenSubspace.IsBaseChange B S hS f h p q)
    (Hr : AlgebraicGeometry.Space.FiniteOpenSubspace.IsBaseChange B S hS f h p r) : q = r := by
  obtain ⟨aq, Zq, hq, fq⟩ := q
  obtain ⟨ar, Zr, hr, fr⟩ := r
  have hab : aq = ar := ObjectProperty.hom_ext _ (Hq.1.trans Hr.1.symm)
  cases hab
  obtain ⟨_, kq, hqpb, hqX⟩ := Hq
  obtain ⟨_, kr, hrpb, hrX⟩ := Hr
  dsimp only at kq kr hqpb hrpb hqX hrX
  let e := hqpb.isoIsPullback _ _ hrpb
  have he : e.hom ≫ Zr.ι = Zq.ι := by
    apply pullback.hom_ext
    · exact IsPullback.isoIsPullback_hom_fst _ _ hqpb hrpb
    · rw [Category.assoc, ← hrX, ← Category.assoc e.hom kr,
        (IsPullback.isoIsPullback_hom_snd _ _ hqpb hrpb), hqX]
  have hle : ∀ (Z Z' : Subfunctor (pullback aq.hom f.hom)) (k : Z.toFunctor ⟶ Z'.toFunctor),
      k ≫ Z'.ι = Z.ι → Z ≤ Z' := by
    intro Z Z' k hk U x hx
    have hx' := congrArg (fun t => t.app U ⟨x, hx⟩) hk
    change (k.app U ⟨x, hx⟩).val = x at hx'
    exact hx' ▸ (k.app U ⟨x, hx⟩).property
  have hZ : Zq = Zr :=
    le_antisymm (hle _ _ e.hom he) (hle _ _ e.inv (by rw [← he]; simp))
  cases hZ
  rfl

private theorem subfunctor_range_comp_injective
    {C : Type*} [Category C] {F G : C ⥤ Type u}
    (g : F ⟶ G) [Mono g] (A D : Subfunctor F)
    (h : Subfunctor.range (A.ι ≫ g) = Subfunctor.range (D.ι ≫ g)) : A = D := by
  have hinj (U : C) : Function.Injective (g.app U) :=
    (mono_iff_injective _).mp inferInstance
  have key : ∀ A D : Subfunctor F, Subfunctor.range (A.ι ≫ g) ≤ Subfunctor.range (D.ι ≫ g) →
      A ≤ D := by
    intro A D hAD U x hx
    obtain ⟨d, hd⟩ := hAD U ⟨⟨x, hx⟩, rfl⟩
    have hdx : d.val = x := hinj U hd
    exact hdx ▸ d.property
  exact le_antisymm (key A D h.le) (key D A h.ge)

private theorem finiteOpenImagePair_injective
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (j : X' ⟶ X) (f' : X' ⟶ Y) (f : X ⟶ Y)
    (hj : j ≫ f = f') (hjOpen : AlgebraicGeometry.Space.IsOpenImmersion B S hS j.hom)
    (T : AlgebraicGeometry.BigFppfOver B S hS) :
    Function.Injective (finiteOpenImagePair B S hS T j f' f hj hjOpen) := by
  intro p q H
  obtain ⟨ap, Zp, hp, fp⟩ := p
  obtain ⟨aq, Zq, hq, fq⟩ := q
  have ha : ap = aq := congrArg AlgebraicGeometry.Space.FiniteOpenSubspace.toBase H
  cases ha
  have hZ : Zp = Zq := by
    let g := finiteOpenAmbientMap B S hS ap j f' f hj
    have : Mono g := mono_of_openImmersion B S hS g
      (finiteOpenAmbientMap_isOpenImmersion B S hS ap j f' f hj hjOpen)
    apply subfunctor_range_comp_injective g
    have hsub := congrArg (fun z =>
      (⟨z.toBase, z.subspace⟩ : Σ a :
        AlgebraicGeometry.schemeSpace T ⟶ Y,
          Subfunctor (pullback a.hom f.hom))) H
    exact eq_of_heq (Sigma.mk.inj hsub).2
  cases hZ
  rfl

private theorem finiteOpenImagePair_map
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (j : X' ⟶ X) (f' : X' ⟶ Y) (f : X ⟶ Y)
    (hj : j ≫ f = f') (hjOpen : AlgebraicGeometry.Space.IsOpenImmersion B S hS j.hom)
    {T T' : AlgebraicGeometry.BigFppfOver B S hS} (h : T' ⟶ T)
    (s : (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f').toFunctor.obj (op T)) :
    finiteOpenImagePair B S hS T' j f' f hj hjOpen
        ((AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f').sections T'
          ((AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f').toFunctor.map h.op s)) =
      (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f).sections T'
        ((AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f).toFunctor.map h.op
          (((AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f).sections T).symm
            (finiteOpenImagePair B S hS T j f' f hj hjOpen
              ((AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f').sections T s)))) := by
  let P := AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f'
  let Q := AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f
  let p := P.sections T s
  let q := P.sections T' (P.toFunctor.map h.op s)
  let c := (Q.sections T).symm (finiteOpenImagePair B S hS T j f' f hj hjOpen p)
  have Hsource : AlgebraicGeometry.Space.FiniteOpenSubspace.IsBaseChange B S hS f' h p q := by
    simpa [P] using P.map_isBaseChange h s
  have Hmapped : AlgebraicGeometry.Space.FiniteOpenSubspace.IsBaseChange B S hS f h
      (finiteOpenImagePair B S hS T j f' f hj hjOpen p)
      (Q.sections T' (Q.toFunctor.map h.op c)) := by
    simpa [c, P, Q, p] using Q.map_isBaseChange h c
  exact finiteOpenSubspace_eq_of_isBaseChange B S hS f h _ _ _
    (finiteOpenImagePair_isBaseChange B S hS j f' f hj hjOpen h p q Hsource) Hmapped

/-- The canonical injective map `(X'/Y)₍fin₎ ⟶ (X/Y)₍fin₎` induced by an
open immersion `X' ⟶ X` over `Y`. Its specification identifies each image
finite open pair over a test scheme. -/
@[stacks 04PF]
public noncomputable def finiteOpenSubspaceMap
    (B : AlgebraicGeometry.BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {X' X Y : AlgebraicGeometry.AlgebraicSpaces B S hS}
    (j : X' ⟶ X) (f' : X' ⟶ Y) (f : X ⟶ Y)
    (hj : j ≫ f = f') (hjOpen : AlgebraicGeometry.Space.IsOpenImmersion B S hS j.hom) :
    { m : (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f').toFunctor ⟶
        (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f).toFunctor //
      Mono m ∧
        ∀ (T : AlgebraicGeometry.BigFppfOver B S hS)
          (s : (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f').toFunctor.obj (op T)),
          let p := (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f').sections T s
          let q := (AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f).sections T
            (m.app (op T) s)
          (p.toBase = q.toBase) ∧
            ∃ k : p.subspace.toFunctor ⟶ q.subspace.toFunctor,
              IsIso k ∧
                (k ≫ q.subspace.ι ≫ pullback.fst q.toBase.hom f.hom =
                  p.subspace.ι ≫ pullback.fst p.toBase.hom f'.hom) ∧
                (k ≫ q.subspace.ι ≫ pullback.snd q.toBase.hom f.hom =
                  p.subspace.ι ≫ pullback.snd p.toBase.hom f'.hom ≫ j.hom) } := by
  classical
  let P := AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f'
  let Q := AlgebraicGeometry.Space.finiteOpenSubspacePresheaf B S hS f
  let component (T : AlgebraicGeometry.BigFppfOver B S hS)
      (s : P.toFunctor.obj (op T)) :=
    (Q.sections T).symm (finiteOpenImagePair B S hS T j f' f hj hjOpen
      (P.sections T s))
  let m : P.toFunctor ⟶ Q.toFunctor := {
    app := fun T => ↾fun s => component T.unop s
    naturality := by
      intro T T' g
      ext s
      change component T'.unop (P.toFunctor.map g s) =
        Q.toFunctor.map g (component T.unop s)
      apply (Q.sections T'.unop).injective
      simpa [component, P, Q] using finiteOpenImagePair_map B S hS j f' f hj hjOpen g.unop s }
  refine ⟨m, ?_, ?_⟩
  · apply (NatTrans.mono_iff_mono_app m).mpr
    intro T
    apply (mono_iff_injective _).mpr
    intro s t hst
    apply (P.sections T.unop).injective
    apply finiteOpenImagePair_injective B S hS j f' f hj hjOpen T.unop
    simpa [m, component] using congrArg (Q.sections T.unop) hst
  · intro T s
    let p := P.sections T s
    let q := Q.sections T (m.app (op T) s)
    have hq : q = finiteOpenImagePair B S hS T j f' f hj hjOpen p := by
      simp [q, m, component, P, Q, p, Equiv.apply_symm_apply]
    dsimp only [q, Q] at hq
    dsimp only
    rw [hq]
    obtain ⟨e, he₁, he₂⟩ := finiteOpenImagePair_iso B S hS j f' f hj hjOpen T p
    exact ⟨rfl, e.hom, inferInstance, he₁, he₂⟩

end AlgebraicGeometry.Space

end
