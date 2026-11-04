module

public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeGluingUniqueness
public import StacksFrontier.AlgebraicGeometry.Constructions.RelativeSheafGluing
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentPullbackScheme

/-!
# Uniqueness of the relatively glued pair

Fix a locally directed open cover `𝒰` of a scheme `S`, a relative gluing datum `d` over it, and a
compatible family `D` of quasi-coherent modules on the schemes of `d`.  Tag 01LI asserts that
there is a scheme `X` over `S` glued from `d` carrying a quasi-coherent module `F` which induces
the prescribed local modules and their transition isomorphisms, and that **the pair `(X, F)` is
unique up to unique isomorphism over `S`**.

Existence is
`Stacks.AlgebraicGeometry.RelativeSheafGluing.RelativeSheafGluingData.exists_isPullback_localIso`.
The two halves of the uniqueness assertion were available separately: uniqueness of the total
space with its charts across different total spaces
(`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.existsUnique_iso`) and uniqueness of the
module over the *canonical* total space
(`RelativeSheafGluingData.existsUnique_iso_realization`).  Neither mentions the other's data, and
the second is tied to the canonical total space because
`RelativeSheafGluingData.Realization.sheaf` lives on
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.glued`.  This file supplies the missing
combination.

## Main definitions

* `RelativeSheafGluingData.RealizationOn`: a realization of `D` on an *arbitrary* gluing `G` of
  `d`, i.e. a quasi-coherent module on `G.pt` inducing the prescribed local modules and
  transition isomorphisms through the charts of `G`.  Taken on the canonical gluing this is
  `RelativeSheafGluingData.Realization`.
* `RelativeSheafGluingData.RealizationOn.transportOn`: the inverse image of a realization along an
  isomorphism of gluings, which is a realization on the source gluing.
* `RelativeSheafGluingData.PairIso`: an isomorphism of glued pairs — an isomorphism of total
  spaces over `S` carrying the charts to the charts, together with an isomorphism of the glued
  modules carrying the local identifications to the local identifications.

## Main results

* `RelativeSheafGluingData.existsUnique_iso_realizationOn`: two realizations on one gluing are
  related by exactly one isomorphism compatible with the local identifications.  This is
  `RelativeSheafGluingData.existsUnique_iso_realization` moved off the canonical total space.
* `RelativeSheafGluingData.existsUnique_pairIso`: **the pair `(X, F)` is unique up to unique
  isomorphism over `S`** — the "moreover" sentence of Tag 01LI.
* `RelativeSheafGluingData.exists_glued_and_existsUnique_pairIso`: **both assertions of Tag 01LI
  as one statement** — existence of the whole glued package, and uniqueness of the pair `(X, F)`
  up to unique isomorphism over `S`.

## Implementation notes

The obstruction to combining the two halves is that a realization is pinned to the canonical
total space, so a module on one gluing cannot be compared with a module on another.  It is removed
by `RealizationOn`, which states the same data against the charts of an arbitrary gluing, together
with the transport of a realization along an isomorphism of gluings: pulling the module back along
the isomorphism and composing the local identifications with the comparison
`Stacks.AlgebraicGeometry.RelativeSheafGluing.transportNatIso` of an iterated inverse image with
the inverse image of a composite.  That the transported local identifications still recover the
prescribed transition isomorphisms is the pseudofunctor associativity coherence
`AlgebraicGeometry.Scheme.Modules.pseudofunctor_associativity`, repackaged as
`transport_coherence`.

With transport available, uniqueness on an arbitrary gluing reduces to uniqueness on the
canonical one: pull both realizations back along a comparison of the gluing with the canonical
gluing, apply `RelativeSheafGluingData.existsUnique_iso_realization`, and descend the resulting
isomorphism, using that inverse image along an isomorphism of schemes is fully faithful.  Pair
uniqueness is then the total-space half together with uniqueness on the one gluing obtained by
transporting the second module to the first total space.

## References

* [Stacks Project, Tag 01LI](https://stacks.math.columbia.edu/tag/01LI)
-/

@[expose] public noncomputable section

universe u

open CategoryTheory Limits

open AlgebraicGeometry AlgebraicGeometry.Scheme.Cover.RelativeGluingData

namespace Stacks.AlgebraicGeometry.RelativeSheafGluing

section Pullback

variable {X Y : Scheme.{u}}

/-- The inverse image along `e.inv` of the inverse image along `e.hom` is the module itself. -/
def pullbackHomInv (e : X ≅ Y) :
    Scheme.Modules.pullback e.hom ⋙ Scheme.Modules.pullback e.inv ≅ 𝟭 Y.Modules :=
  Scheme.Modules.pullbackComp e.inv e.hom ≪≫
    Scheme.Modules.pullbackCongr e.inv_hom_id ≪≫ Scheme.Modules.pullbackId Y

/-- The inverse image along `e.hom` of the inverse image along `e.inv` is the module itself. -/
def pullbackInvHom (e : X ≅ Y) :
    Scheme.Modules.pullback e.inv ⋙ Scheme.Modules.pullback e.hom ≅ 𝟭 X.Modules :=
  Scheme.Modules.pullbackComp e.hom e.inv ≪≫
    Scheme.Modules.pullbackCongr e.hom_inv_id ≪≫ Scheme.Modules.pullbackId X

/-- **Inverse image along an isomorphism of schemes is an equivalence** of the categories of
modules. -/
def pullbackEquivalence (e : X ≅ Y) : Y.Modules ≌ X.Modules :=
  CategoryTheory.Equivalence.mk (Scheme.Modules.pullback e.hom)
    (Scheme.Modules.pullback e.inv) (pullbackHomInv e).symm (pullbackInvHom e)

/-- **Inverse image along an isomorphism of schemes is fully faithful.** -/
def pullbackFullyFaithful (e : X ≅ Y) : (Scheme.Modules.pullback e.hom).FullyFaithful :=
  (pullbackEquivalence e).fullyFaithfulFunctor

end Pullback

section Transport

variable {Xi Xj P P' : Scheme.{u}}

/-- The comparison identifying the inverse image along `c` of the inverse image along `r` with the
inverse image along a morphism `c'` which equals the composite `c ≫ r`.  Transporting a module
along `r` moves a local identification over `c'` to one over `c` through this comparison. -/
def transportNatIso (c : Xi ⟶ P) (r : P ⟶ P') (c' : Xi ⟶ P') (hc : c ≫ r = c') :
    Scheme.Modules.pullback r ⋙ Scheme.Modules.pullback c ≅ Scheme.Modules.pullback c' :=
  Scheme.Modules.pullbackComp c r ≪≫ Scheme.Modules.pullbackCongr hc

/-- `Stacks.AlgebraicGeometry.RelativeSheafGluing.transportNatIso` at one module, with the
iterated inverse image spelled out. -/
def transportIso (c : Xi ⟶ P) (r : P ⟶ P') (c' : Xi ⟶ P') (hc : c ≫ r = c') (M : P'.Modules) :
    (Scheme.Modules.pullback c).obj ((Scheme.Modules.pullback r).obj M) ≅
      (Scheme.Modules.pullback c').obj M :=
  (transportNatIso c r c' hc).app M

/-- The transport comparison is natural in the module. -/
lemma transportIso_inv_naturality (c : Xi ⟶ P) (r : P ⟶ P') (c' : Xi ⟶ P') (hc : c ≫ r = c')
    {M N : P'.Modules} (φ : M ⟶ N) :
    (transportIso c r c' hc M).inv ≫
        (Scheme.Modules.pullback c).map ((Scheme.Modules.pullback r).map φ) =
      (Scheme.Modules.pullback c').map φ ≫ (transportIso c r c' hc N).inv := by
  have h := (transportNatIso c r c' hc).hom.naturality φ
  simp only [Functor.comp_map] at h
  refine (cancel_mono (transportIso c r c' hc N).hom).1 ?_
  simp only [transportIso, Iso.app_hom, Iso.app_inv, Category.assoc]
  rw [h, Iso.inv_hom_id_app_assoc, Iso.inv_hom_id_app, Category.comp_id]

/-- **The associativity coherence behind transport of local identifications.**  Comparing the
inverse image along `q'` with the iterated inverse image along `q` and `r`, pushing the result
along `p`, and then comparing the iterated inverse image along `p ≫ q` and `r` with the inverse
image along `c'`, is the same as comparing the iterated inverse image along `p` and `q'` with the
inverse image along `c'` directly. -/
private lemma transport_coherence_aux
    (p : Xi ⟶ Xj) (q : Xj ⟶ P) (r : P ⟶ P') (c : Xi ⟶ P) (q' : Xj ⟶ P') (c' : Xi ⟶ P')
    (hc : p ≫ q = c) (hq' : q ≫ r = q') (hc' : c ≫ r = c') (M : P'.Modules) :
    (Scheme.Modules.pullback p).map ((Scheme.Modules.pullbackCongr hq').inv.app M ≫
            (Scheme.Modules.pullbackComp q r).inv.app M) ≫
          (Scheme.Modules.pullbackComp p q).hom.app ((Scheme.Modules.pullback r).obj M) ≫
            (Scheme.Modules.pullbackCongr hc).hom.app ((Scheme.Modules.pullback r).obj M) ≫
              (Scheme.Modules.pullbackComp c r).hom.app M ≫
                (Scheme.Modules.pullbackCongr hc').hom.app M =
      (Scheme.Modules.pullbackComp p q').hom.app M ≫
        (Scheme.Modules.pullbackCongr
          (show p ≫ q' = c' by rw [← hq', ← Category.assoc, hc, hc'])).hom.app M := by
  subst hc hq' hc'
  simp only [Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom, Iso.refl_inv,
    NatTrans.id_app, Category.id_comp, Category.comp_id]
  have key := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity p q r) M
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.whiskerLeft_app,
    Functor.associator_hom_app, Category.id_comp, eqToHom_app] at key
  simpa only [Iso.app_hom, eqToIso.hom, eqToHom_app] using
    (Iso.inv_comp_eq (Iso.app (Scheme.Modules.pullbackComp p (q ≫ r)) M)).1 key

/-- `Stacks.AlgebraicGeometry.RelativeSheafGluing.transport_coherence_aux`, read through the
comparison `Stacks.AlgebraicGeometry.RelativeSheafGluing.transportNatIso`. -/
lemma transport_coherence
    (p : Xi ⟶ Xj) (q : Xj ⟶ P) (r : P ⟶ P') (c : Xi ⟶ P) (q' : Xj ⟶ P') (c' : Xi ⟶ P')
    (hc : p ≫ q = c) (hq' : q ≫ r = q') (hc' : c ≫ r = c') (M : P'.Modules) :
    (Scheme.Modules.pullback p).map (transportIso q r q' hq' M).inv ≫
          (Scheme.Modules.pullbackComp p q).hom.app ((Scheme.Modules.pullback r).obj M) ≫
            (Scheme.Modules.pullbackCongr hc).hom.app ((Scheme.Modules.pullback r).obj M) ≫
              (transportIso c r c' hc' M).hom =
      (Scheme.Modules.pullbackComp p q').hom.app M ≫
        (Scheme.Modules.pullbackCongr
          (show p ≫ q' = c' by rw [← hq', ← Category.assoc, hc, hc'])).hom.app M := by
  simpa only [transportIso, transportNatIso, Iso.app_hom, Iso.app_inv, Iso.trans_hom,
    Iso.trans_inv,
    NatTrans.comp_app, Category.assoc] using
      transport_coherence_aux p q r c q' c' hc hq' hc' M

end Transport

variable {S : Scheme.{u}} {𝒰 : S.OpenCover} [Category 𝒰.I₀] [𝒰.LocallyDirected]
  [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀]

namespace RelativeSheafGluingData

variable {d : Scheme.Cover.RelativeGluingData 𝒰} (D : RelativeSheafGluingData d)

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- **The transported local identifications still recover the prescribed transition
isomorphisms.**  Stated for bare chart families rather than for gluings, so that it serves both
the transport between two gluings and the transport to the canonical relatively glued scheme. -/
lemma transport_compatible {X Y : Scheme.{u}}
    (cX : ∀ i, d.functor.obj i ⟶ X) (cY : ∀ i, d.functor.obj i ⟶ Y)
    (htX : ∀ {i j : 𝒰.I₀} (hij : i ⟶ j), d.functor.map hij ≫ cX j = cX i)
    (htY : ∀ {i j : 𝒰.I₀} (hij : i ⟶ j), d.functor.map hij ≫ cY j = cY i)
    (r : X ⟶ Y) (hr : ∀ i, cX i ≫ r = cY i) (N : Y.Modules)
    (localIso : ∀ i, D.obj i ≅ (Scheme.Modules.pullback (cY i)).obj N)
    (compat : ∀ {i j : 𝒰.I₀} (hij : i ⟶ j),
      (D.transitionIso hij).hom ≫ (localIso i).hom =
        (Scheme.Modules.pullback (d.functor.map hij)).map (localIso j).hom ≫
          (Scheme.Modules.pullbackComp (d.functor.map hij) (cY j)).hom.app N ≫
            (Scheme.Modules.pullbackCongr (htY hij)).hom.app N)
    {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (D.transitionIso hij).hom ≫
        (localIso i ≪≫ (transportIso (cX i) r (cY i) (hr i) N).symm).hom =
      (Scheme.Modules.pullback (d.functor.map hij)).map
          (localIso j ≪≫ (transportIso (cX j) r (cY j) (hr j) N).symm).hom ≫
        (Scheme.Modules.pullbackComp (d.functor.map hij) (cX j)).hom.app
            ((Scheme.Modules.pullback r).obj N) ≫
          (Scheme.Modules.pullbackCongr (htX hij)).hom.app ((Scheme.Modules.pullback r).obj N) := by
  have coh := transport_coherence (d.functor.map hij) (cX j) r (cX i) (cY j) (cY i)
    (htX hij) (hr j) (hr i) N
  refine (cancel_mono (transportIso (cX i) r (cY i) (hr i) N).hom).1 ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Functor.map_comp, Category.assoc,
    Iso.inv_hom_id, Category.comp_id]
  rw [coh, compat hij]

/-- A **realization of relative sheaf gluing on an arbitrary gluing** `G` of the datum: a
quasi-coherent module on the total space of `G` whose inverse image on the `i`-th chart of `G` is
identified with the `i`-th prescribed module, compatibly with the prescribed transition
isomorphisms.  On the canonical gluing this is `RelativeSheafGluingData.Realization`. -/
structure RealizationOn (G : Gluing d) where
  /-- The glued module. -/
  sheaf : G.pt.Modules
  /-- The glued module is quasi-coherent. -/
  isQuasicoherent : sheaf.IsQuasicoherent
  /-- Identification of each prescribed local module with the restriction of the glued one. -/
  localIso : ∀ i, D.obj i ≅ (Scheme.Modules.pullback (G.chart i)).obj sheaf
  /-- The local identifications recover the prescribed transition isomorphisms. -/
  compatible : ∀ {i j} (hij : i ⟶ j),
    (D.transitionIso hij).hom ≫ (localIso i).hom =
      (Scheme.Modules.pullback (d.functor.map hij)).map (localIso j).hom ≫
        (Scheme.Modules.pullbackComp (d.functor.map hij) (G.chart j)).hom.app sheaf ≫
          (Scheme.Modules.pullbackCongr (G.chart_trans hij)).hom.app sheaf

namespace RealizationOn

variable {G G' : Gluing d}

/-- **The inverse image of a realization along an isomorphism of gluings.**  Given a realization
on `G'` and an isomorphism `e : G.pt ≅ G'.pt` carrying the charts of `G` to the charts of `G'`,
pulling the module back along `e` gives a realization on `G`. -/
def transportOn (R : D.RealizationOn G') (e : G.pt ≅ G'.pt)
    (he : ∀ i, G.chart i ≫ e.hom = G'.chart i) : D.RealizationOn G where
  sheaf := (Scheme.Modules.pullback e.hom).obj R.sheaf
  isQuasicoherent :=
    have := R.isQuasicoherent
    Stacks.Modules.isQuasicoherent_pullback e.hom R.sheaf R.isQuasicoherent
  localIso i :=
    R.localIso i ≪≫ (transportIso (G.chart i) e.hom (G'.chart i) (he i) R.sheaf).symm
  compatible hij :=
    D.transport_compatible G.chart G'.chart (fun hij => G.chart_trans hij)
      (fun hij => G'.chart_trans hij) e.hom he R.sheaf R.localIso
      (fun hij => R.compatible hij) hij

/-- `RelativeSheafGluingData.transport_compatible` for the charts of the canonical relatively
glued scheme: exactly the compatibility that `RelativeSheafGluingData.Realization` asks for. -/
lemma transport_compatible_glued (R : D.RealizationOn G) (e : d.glued ≅ G.pt)
    (he : ∀ i, colimit.ι d.functor i ≫ e.hom = G.chart i) {i j : 𝒰.I₀} (hij : i ⟶ j) :
    (D.transitionIso hij).hom ≫
        (R.localIso i ≪≫
          (transportIso (colimit.ι d.functor i) e.hom (G.chart i) (he i) R.sheaf).symm).hom =
      (Scheme.Modules.pullback (d.functor.map hij)).map
          (R.localIso j ≪≫
            (transportIso (colimit.ι d.functor j) e.hom (G.chart j) (he j) R.sheaf).symm).hom ≫
        (Scheme.Modules.pullbackComp (d.functor.map hij) (colimit.ι d.functor j)).hom.app
            ((Scheme.Modules.pullback e.hom).obj R.sheaf) ≫
          (Scheme.Modules.pullbackCongr (colimit.w d.functor hij)).hom.app
            ((Scheme.Modules.pullback e.hom).obj R.sheaf) :=
  D.transport_compatible (colimit.ι d.functor) G.chart (colimit.w d.functor)
    (fun hij => G.chart_trans hij) e.hom he R.sheaf R.localIso
    (fun hij => R.compatible hij) hij

/-- **The inverse image of a realization on the canonical total space.**  Given a realization on
`G` and a comparison `e` of the canonical relatively glued scheme with the total space of `G`
carrying the canonical charts to the charts of `G`, pulling the module back along `e` gives a
realization in the sense of `RelativeSheafGluingData.Realization`. -/
def toRealization (R : D.RealizationOn G) (e : d.glued ≅ G.pt)
    (he : ∀ i, colimit.ι d.functor i ≫ e.hom = G.chart i) : D.Realization where
  sheaf := (Scheme.Modules.pullback e.hom).obj R.sheaf
  isQuasicoherent :=
    Stacks.Modules.isQuasicoherent_pullback e.hom R.sheaf R.isQuasicoherent
  localIso i :=
    R.localIso i ≪≫
      (transportIso (colimit.ι d.functor i) e.hom (G.chart i) (he i) R.sheaf).symm
  compatible hij := transport_compatible_glued D R e he hij

end RealizationOn

/-- **Every gluing of the datum is comparable to the canonical one.**  This is
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.existsUnique_iso` at the canonical gluing
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.gluingGlued`, spelled with the colimit
charts. -/
lemma exists_glued_iso (G : Gluing d) :
    ∃ e : d.glued ≅ G.pt, (∀ i, colimit.ι d.functor i ≫ e.hom = G.chart i) ∧
      e.hom ≫ G.toBase = d.toBase :=
  ⟨(gluingGlued d).iso G, fun i => (gluingGlued d).chart_glue G i,
    (gluingGlued d).glue_toBase G⟩

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- **Transport does not change which isomorphisms are compatible with the local
identifications.**  Stated for bare chart families: an isomorphism of two modules on `Y`, pulled
back along `r`, is compatible with the transported local identifications exactly when it is
compatible with the original ones. -/
lemma compatible_transport_iff {X Y : Scheme.{u}} (cX : ∀ i, d.functor.obj i ⟶ X)
    (cY : ∀ i, d.functor.obj i ⟶ Y) (r : X ⟶ Y) (hr : ∀ i, cX i ≫ r = cY i) {M N : Y.Modules}
    (lM : ∀ i, D.obj i ≅ (Scheme.Modules.pullback (cY i)).obj M)
    (lN : ∀ i, D.obj i ≅ (Scheme.Modules.pullback (cY i)).obj N) (φ : M ≅ N) :
    (∀ i, (lM i ≪≫ (transportIso (cX i) r (cY i) (hr i) M).symm).hom ≫
          (Scheme.Modules.pullback (cX i)).map ((Scheme.Modules.pullback r).map φ.hom) =
        (lN i ≪≫ (transportIso (cX i) r (cY i) (hr i) N).symm).hom) ↔
      ∀ i, (lM i).hom ≫ (Scheme.Modules.pullback (cY i)).map φ.hom = (lN i).hom := by
  refine forall_congr' fun i => ?_
  simp only [Iso.trans_hom, Iso.symm_hom, Category.assoc,
    transportIso_inv_naturality (cX i) r (cY i) (hr i) φ.hom]
  rw [← Category.assoc]
  exact cancel_mono (transportIso (cX i) r (cY i) (hr i) N).inv

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- **The two readings of compatibility with a transported local identification.**  Stated for
bare chart families: an isomorphism of a module on `X` with the inverse image along `r` of a
module on `Y` is compatible with the transported local identifications exactly when, followed by
the transport comparison, it carries the one family of local identifications to the other. -/
lemma compatible_transportOn_iff {X Y : Scheme.{u}} (cX : ∀ i, d.functor.obj i ⟶ X)
    (cY : ∀ i, d.functor.obj i ⟶ Y) (r : X ⟶ Y) (hr : ∀ i, cX i ≫ r = cY i) {M : X.Modules}
    {N : Y.Modules} (lM : ∀ i, D.obj i ≅ (Scheme.Modules.pullback (cX i)).obj M)
    (lN : ∀ i, D.obj i ≅ (Scheme.Modules.pullback (cY i)).obj N)
    (φ : M ≅ (Scheme.Modules.pullback r).obj N) :
    (∀ i, (lM i).hom ≫ (Scheme.Modules.pullback (cX i)).map φ.hom =
        (lN i ≪≫ (transportIso (cX i) r (cY i) (hr i) N).symm).hom) ↔
      ∀ i, (lM i).hom ≫ (Scheme.Modules.pullback (cX i)).map φ.hom ≫
          (transportIso (cX i) r (cY i) (hr i) N).hom = (lN i).hom := by
  refine forall_congr' fun i => ?_
  simp only [Iso.trans_hom, Iso.symm_hom]
  refine ⟨fun h => ?_, fun h => ?_⟩
  · rw [← Category.assoc, h, Category.assoc, Iso.inv_hom_id, Category.comp_id]
  · rw [← h, Category.assoc, Category.assoc, Iso.hom_inv_id, Category.comp_id]

variable {G G' : Gluing d}

/-- `RelativeSheafGluingData.compatible_transport_iff` for the charts of the canonical relatively
glued scheme: the compatibility that `RelativeSheafGluingData.existsUnique_iso_realization` asks
of an isomorphism of the transported realizations is the compatibility asked of the isomorphism
it is the inverse image of. -/
lemma compatible_toRealization_iff (R R₂ : D.RealizationOn G) (e : d.glued ≅ G.pt)
    (he : ∀ i, colimit.ι d.functor i ≫ e.hom = G.chart i) (φ : R.sheaf ≅ R₂.sheaf) :
    (∀ i, ((RealizationOn.toRealization D R e he).localIso i).hom ≫
          (Scheme.Modules.pullback (colimit.ι d.functor i)).map
            ((Scheme.Modules.pullback e.hom).map φ.hom) =
        ((RealizationOn.toRealization D R₂ e he).localIso i).hom) ↔
      ∀ i, (R.localIso i).hom ≫ (Scheme.Modules.pullback (G.chart i)).map φ.hom =
        (R₂.localIso i).hom :=
  D.compatible_transport_iff (colimit.ι d.functor) G.chart e.hom he R.localIso R₂.localIso φ

/-- **Stacks Project, Tag 01LI.**  *Uniqueness of the glued module on an arbitrary total space.*
Two realizations of `D` on one gluing `G` of `d` are related by exactly one isomorphism of the
glued modules whose inverse image on each chart of `G` carries the local identifications of the
one to those of the other.

This is `RelativeSheafGluingData.existsUnique_iso_realization` moved off the canonical total
space: both realizations are pulled back along a comparison of `G` with the canonical gluing, and
the resulting isomorphism is descended using that inverse image along an isomorphism of schemes is
fully faithful. -/
theorem existsUnique_iso_realizationOn (R R₂ : D.RealizationOn G) :
    ∃! φ : R.sheaf ≅ R₂.sheaf,
      ∀ i, (R.localIso i).hom ≫ (Scheme.Modules.pullback (G.chart i)).map φ.hom =
        (R₂.localIso i).hom := by
  obtain ⟨e, he, -⟩ := exists_glued_iso G
  have hff := pullbackFullyFaithful e
  obtain ⟨ε, hε, huniq⟩ :=
    D.existsUnique_iso_realization (RealizationOn.toRealization D R e he)
      (RealizationOn.toRealization D R₂ e he)
  refine ⟨hff.preimageIso ε, (compatible_toRealization_iff D R R₂ e he _).1 ?_, fun φ hφ => ?_⟩
  · intro i
    have hmap : (Scheme.Modules.pullback e.hom).map (hff.preimageIso ε).hom = ε.hom :=
      hff.map_preimage ε.hom
    rw [hmap]
    exact hε i
  · have h1 : (Scheme.Modules.pullback e.hom).mapIso φ = ε :=
      huniq _ ((compatible_toRealization_iff D R R₂ e he φ).2 hφ)
    rw [← h1]
    simpa using (hff.isoEquiv.symm_apply_apply φ).symm

/-- An **isomorphism of glued pairs**: an isomorphism of the two total spaces over `S` carrying
the charts of the one to the charts of the other, together with an isomorphism of the two glued
modules carrying the local identifications of the one to those of the other. -/
structure PairIso (R : D.RealizationOn G) (R' : D.RealizationOn G') where
  /-- The isomorphism of total spaces. -/
  base : G.pt ≅ G'.pt
  /-- The isomorphism of total spaces is a morphism over the base. -/
  base_toBase : base.hom ≫ G'.toBase = G.toBase
  /-- The isomorphism of total spaces carries the charts to the charts. -/
  base_chart : ∀ i, G.chart i ≫ base.hom = G'.chart i
  /-- The isomorphism of glued modules. -/
  sheaf : R.sheaf ≅ (Scheme.Modules.pullback base.hom).obj R'.sheaf
  /-- The isomorphism of glued modules carries the local identifications to the local
  identifications. -/
  sheaf_localIso : ∀ i, (R.localIso i).hom ≫
        (Scheme.Modules.pullback (G.chart i)).map sheaf.hom ≫
          (transportIso (G.chart i) base.hom (G'.chart i) (base_chart i) R'.sheaf).hom =
      (R'.localIso i).hom

omit [Small.{u} 𝒰.I₀] [Quiver.IsThin 𝒰.I₀] in
/-- `RelativeSheafGluingData.compatible_transportOn_iff` for the charts of two gluings: the
compatibility asked of the module half of an isomorphism of glued pairs is the compatibility that
`RelativeSheafGluingData.existsUnique_iso_realizationOn` asks for the second realization
transported to the first total space. -/
lemma pairIso_sheaf_condition_iff (R : D.RealizationOn G) (R' : D.RealizationOn G')
    (e : G.pt ≅ G'.pt) (he : ∀ i, G.chart i ≫ e.hom = G'.chart i)
    (φ : R.sheaf ≅ (Scheme.Modules.pullback e.hom).obj R'.sheaf) :
    (∀ i, (R.localIso i).hom ≫ (Scheme.Modules.pullback (G.chart i)).map φ.hom =
        ((RealizationOn.transportOn D R' e he).localIso i).hom) ↔
      ∀ i, (R.localIso i).hom ≫ (Scheme.Modules.pullback (G.chart i)).map φ.hom ≫
          (transportIso (G.chart i) e.hom (G'.chart i) (he i) R'.sheaf).hom =
        (R'.localIso i).hom :=
  D.compatible_transportOn_iff G.chart G'.chart e.hom he R.localIso R'.localIso φ

/-- **Stacks Project, Tag 01LI.**  *Uniqueness of the pair.*  Let `𝒰` be a locally directed open
cover of a scheme `S`, let `d` be a relative gluing datum over it, and let `D` be a compatible
family of quasi-coherent modules on the schemes of `d`.  Two glued pairs — a scheme over `S`
glued from `d` together with a quasi-coherent module on it inducing the prescribed local modules
and transition isomorphisms — are related by exactly one isomorphism of pairs: exactly one
isomorphism of the total spaces over `S` carrying the charts to the charts, carrying the glued
module of the one to the glued module of the other compatibly with the local identifications.

This is the "moreover" sentence of [Stacks, Tag 01LI], for the pair `(X, F)` and not for either
half alone.  The total-space half is
`AlgebraicGeometry.Scheme.Cover.RelativeGluingData.existsUnique_iso` and the module half on one
fixed total space is `RelativeSheafGluingData.existsUnique_iso_realizationOn`; existence of a
glued pair is `RelativeSheafGluingData.exists_isPullback_localIso`. -/
theorem existsUnique_pairIso (R : D.RealizationOn G) (R' : D.RealizationOn G') :
    ∃ p : D.PairIso R R', ∀ q : D.PairIso R R', q = p := by
  have he : ∀ i, G.chart i ≫ (G.iso G').hom = G'.chart i := fun i => G.chart_glue G' i
  have htb : (G.iso G').hom ≫ G'.toBase = G.toBase := G.glue_toBase G'
  obtain ⟨φ, hφ, huniq⟩ :=
    D.existsUnique_iso_realizationOn R (RealizationOn.transportOn D R' (G.iso G') he)
  refine ⟨⟨G.iso G', htb, he, φ, (pairIso_sheaf_condition_iff D R R' _ he φ).1 hφ⟩, ?_⟩
  rintro ⟨b, hb1, hb2, s, hs⟩
  obtain rfl : b = G.iso G' :=
    (existsUnique_iso G G').unique ⟨hb1, hb2⟩ ⟨htb, he⟩
  obtain rfl : s = φ := huniq s ((pairIso_sheaf_condition_iff D R R' _ he s).2 hs)
  rfl

/-- **Stacks Project, Tag 01LI, both of its assertions as one statement.**  Let `𝒰` be a locally
directed open cover of a scheme `S`, let `d` be a relative gluing datum over it, and let `D` be a
compatible family of quasi-coherent modules on the schemes of `d`.  Then:

* *existence of the whole package.*  There is a morphism of schemes `f : X ⟶ S`, morphisms
  `i a : X a ⟶ X` exhibiting each `X a` as the part of `X` lying over the `a`-th member of the
  cover and compatible with the transition morphisms of `d`, and a quasi-coherent module `F` on
  `X` together with isomorphisms `θ a : F a ≅ (i a)^* F` under which the prescribed transition
  isomorphisms of the `F a` are the ones induced by `F`.
* *uniqueness.*  The pair `(X, F)` is unique up to unique isomorphism over `S`: any two glued
  pairs are related by exactly one isomorphism of pairs.

The two conjuncts are
`Stacks.AlgebraicGeometry.RelativeSheafGluing.RelativeSheafGluingData.exists_isPullback_localIso`
and
`Stacks.AlgebraicGeometry.RelativeSheafGluing.RelativeSheafGluingData.existsUnique_pairIso`. -/
@[stacks 01LI "both assertions of the tag as one statement: existence of the glued package — the
morphism f, the charts i_U, the quasi-coherent module F, the identifications θ_U and their two
compatibilities — and uniqueness of the pair (X, F) up to unique isomorphism over S"]
theorem exists_glued_and_existsUnique_pairIso :
    (∃ (X : Scheme.{u}) (f : X ⟶ S) (i : ∀ a, d.functor.obj a ⟶ X)
      (_ : ∀ a, IsPullback (d.natTrans.app a) (i a) (𝒰.f a) f)
      (hi : ∀ {a b : 𝒰.I₀} (hab : a ⟶ b), d.functor.map hab ≫ i b = i a)
      (F : X.Modules), F.IsQuasicoherent ∧
        ∃ θ : ∀ a, D.obj a ≅ (Scheme.Modules.pullback (i a)).obj F,
          ∀ {a b : 𝒰.I₀} (hab : a ⟶ b),
            (D.transitionIso hab).hom ≫ (θ a).hom =
              (Scheme.Modules.pullback (d.functor.map hab)).map (θ b).hom ≫
                (Scheme.Modules.pullbackComp (d.functor.map hab) (i b)).hom.app F ≫
                  (Scheme.Modules.pullbackCongr (hi hab)).hom.app F) ∧
      ∀ (H H' : Gluing d) (R : D.RealizationOn H) (R' : D.RealizationOn H'),
        ∃ p : D.PairIso R R', ∀ q : D.PairIso R R', q = p :=
  ⟨D.exists_isPullback_localIso, fun _ _ R R' => D.existsUnique_pairIso R R'⟩

end RelativeSheafGluingData

end Stacks.AlgebraicGeometry.RelativeSheafGluing

end
