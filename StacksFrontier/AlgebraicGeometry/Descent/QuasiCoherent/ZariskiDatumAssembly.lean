module

public import StacksFrontier.AlgebraicGeometry.Descent.QuasiCoherent.FpqcAffineOpenRefinement

/-!
# The transitions of the Zariski descent datum of Stacks 023T

`StacksFrontier/AlgebraicGeometry/Descent/QuasiCoherent/FpqcAffineOpenRefinement.lean` reduces the
effectivity half of Stacks 023T to one statement,
`AlgebraicGeometry.QuasicoherentDescentData.ZariskiDescentDatumOverAffineCover`: for every fpqc
covering family `𝒰` of every scheme `S` and every quasi-coherent descent datum `D` for it, a
quasi-coherent descent datum on the affine open covering of `S` whose restriction to the
affine-open refinement is isomorphic to the restriction of `D`.  The *components* of that datum
are supplied there unconditionally, by
`…exists_iso_canonicalDescentFunctor_affineOpen`, so what is missing is the transition
isomorphisms and their cocycle condition.

This file builds the transitions as far as they go before any descent is needed, and discharges
the cocycle condition.  Fix for each member `U a` of the affine open covering a quasi-coherent
module `M a` on `U a` solving the descent problem there — `affineOpenModule`, chosen once and for
all — together with the isomorphism `affineOpenModuleIso` of its canonical descent datum with the
restriction of `D`.  Over a scheme `V` carrying compatible morphisms `g : V ⟶ U a` and
`c : V ⟶ X i` to a member of the affine open covering and to a member of `𝒰`, those data give a
comparison

`localComparison : g^* (M a) ⟶ c^* (D i)`  and its inverse `localComparisonInv`,

and the content of this file is the two properties the comparisons have:

* they are compatible with the transitions of `D` (`localComparison_comp_hom`) — this is the
  statement that `affineOpenModuleIso` is a morphism of descent data, read in the `pullHom`
  spelling;
* they are compatible with pullback (`pullHom_localComparison`) — on the nose, because they are
  written as pullbacks of the components of `affineOpenModuleIso` along the lift into the fibre
  product, so `CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.pullHom_pullHom` applies.

Composing the comparison at `a` with the inverse comparison at `b` gives the candidate transition
`localTransition` of the datum being built, over any `V` which maps compatibly to `U a`, to `U b`
and to some member of `𝒰`; and the two properties above become exactly what a descent datum asks
of its transitions:

* `localTransition_eq`: the transition **does not depend on the member of `𝒰` used to read it
  off**.  This is the cocycle condition of the datum being built: it says that the transitions
  compose, since each of the three is read off the same member of `𝒰`;
* `pullHom_localTransition`: the transition is compatible with pullback, which is the
  `pullHom_hom` condition of a descent datum.

## Main definitions

* `AlgebraicGeometry.QuasicoherentDescentData.affineOpenModule` and
  `…affineOpenModuleIso`: the chosen local solution over each member of the affine open covering
  of the base, and the chosen isomorphism exhibiting it as one.
* `AlgebraicGeometry.QuasicoherentDescentData.localComparison` and `…localComparisonInv`: the
  comparison of the local solution over `U a` with the component of `D` at `X i`, over a scheme
  mapping compatibly to both.
* `AlgebraicGeometry.QuasicoherentDescentData.localTransition`: the candidate transition of the
  Zariski descent datum, read off a member of `𝒰`.

## Main results

* `AlgebraicGeometry.QuasicoherentDescentData.ofObj_hom`,
  `…rawPullFunctor_obj_hom` and `…map_eq_pullHom'`: the transitions of a canonical descent datum
  and of a restricted one, and the pullback of a morphism, all written as conjugates of
  `AlgebraicGeometry.pullModComp` by `pullHom`.  These are the dictionary in which the rest of
  the file is written.
* `AlgebraicGeometry.QuasicoherentDescentData.pullHom_hom_comp_eq`: **a morphism from a canonical
  descent datum to a restricted one intertwines the pullbacks of its components with the
  transition of the restricted datum.**
* `AlgebraicGeometry.QuasicoherentDescentData.localComparison_comp_hom`: **the local comparisons
  are compatible with the transitions of `D`.**
* `AlgebraicGeometry.QuasicoherentDescentData.localTransition_eq`: **the candidate transition is
  independent of the member of `𝒰` it is read off**, which is what turns the cocycle condition of
  the datum being built into a formality.
* `AlgebraicGeometry.QuasicoherentDescentData.localTransition_self` and
  `…localTransition_comp`: **the candidate transitions are the identity at a repeated member and
  compose**, which are the `hom_self` and `hom_comp` conditions of the datum being built.
* `AlgebraicGeometry.QuasicoherentDescentData.pullHom_localTransition`: **the candidate
  transition is compatible with pullback.**

## Implementation notes

Everything is written in the `pullHom` spelling of
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat`, in which the pseudofunctor's coherence is
carried by `pullHom_pullHom` and `pullHom_comp` rather than by hand.  The two comparison
morphisms are given separately, `localComparison` and `localComparisonInv`, rather than one of
them as the inverse of the other, so that each is a pullback of a fixed morphism and hence
compatible with further pullback on the nose; this is the device of
`AlgebraicGeometry.summandCompAt`.

The dictionary lemmas are stated at the level of `CategoryTheory.Pseudofunctor.DescentData` for
the pullback pseudofunctor, not of `AlgebraicGeometry.QuasicoherentDescentData`.  That is not
cosmetic: the quasi-coherent descent data form a `CategoryTheory.ObjectProperty.FullSubcategory`,
and the predicate cutting it out mentions `AlgebraicGeometry.Scheme.ringCatSheaf`, whose type is
not type-correct at the `implicit` transparency level; a conversion that has to pass through it
makes `whnf` loop.  Reading the components of the chosen isomorphism through
`CategoryTheory.ObjectProperty.ι` once, in `affineOpenModuleDescentIso` and `affineOpenComponent`,
keeps that conversion out of every later proof.

What is **not** done here is the descent of `localTransition` from the base change of `𝒰` to the
base itself.  `localTransition` is defined only over a scheme which maps to a member of `𝒰`;
`ZariskiDescentDatumOverAffineCover` asks for a transition over an arbitrary `V ⟶ S`, and over
such a `V` the base change of `𝒰` is an fpqc covering along which the transitions above do
glue — the gluing being the full faithfulness half of Stacks 023T,
`…nonempty_fullyFaithful_canonicalDescentFunctor_of_mem_fpqcPrecoverage`, which is already a
theorem.  `localTransition_eq` and `pullHom_localTransition` are exactly the two hypotheses that
gluing consumes.  No statement of this file assumes anything.

No `stacks` attribute is placed: nothing here is a clause of a tag.

## References

* [Stacks Project, Tag 023T](https://stacks.math.columbia.edu/tag/023T)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite
  Pseudofunctor.LocallyDiscreteOpToCat

universe w₁ w₃ v u

namespace AlgebraicGeometry

namespace QuasicoherentDescentData

/-! ### Reading off the transitions -/

section Transitions

variable {T W : Scheme.{u}} {𝒱 : PreZeroHypercover.{v} T} {𝒳 : PreZeroHypercover.{v} W}

/-- The pullback of a morphism of pullbacks, conjugated back by the comparison isomorphisms:
`CategoryTheory.Pseudofunctor.LocallyDiscreteOpToCat.map_eq_pullHom` read through
`AlgebraicGeometry.pullModComp`. -/
theorem map_eq_pullHom' {Z₁ Z₂ Y Y' : Scheme.{u}}
    {M₁ : modulePullbackPseudofunctor.obj (.mk (op Z₁))}
    {M₂ : modulePullbackPseudofunctor.obj (.mk (op Z₂))} {f₁ : Y ⟶ Z₁} {f₂ : Y ⟶ Z₂}
    (φ : pullMod f₁ M₁ ⟶ pullMod f₂ M₂) (g : Y' ⟶ Y) (gf₁ : Y' ⟶ Z₁) (gf₂ : Y' ⟶ Z₂)
    (h₁ : g ≫ f₁ = gf₁) (h₂ : g ≫ f₂ = gf₂) :
    (modulePullbackPseudofunctor.map g.op.toLoc).toFunctor.map φ =
      (pullModComp g f₁ gf₁ h₁ M₁).inv ≫ pullHom φ g gf₁ gf₂ h₁ h₂ ≫
        (pullModComp g f₂ gf₂ h₂ M₂).hom :=
  map_eq_pullHom φ g gf₁ gf₂ h₁ h₂

/-- **The transition isomorphisms of the canonical descent datum of a sheaf of modules** are the
comparison isomorphisms of the pullback pseudofunctor. -/
theorem ofObj_hom (M : modulePullbackPseudofunctor.obj (.mk (op T)))
    {Y : Scheme.{u}} (q : Y ⟶ T) {i₁ i₂ : 𝒱.I₀} (f₁ : Y ⟶ 𝒱.X i₁) (f₂ : Y ⟶ 𝒱.X i₂)
    (h₁ : f₁ ≫ 𝒱.f i₁ = q) (h₂ : f₂ ≫ 𝒱.f i₂ = q) :
    (Pseudofunctor.DescentData.ofObj (F := modulePullbackPseudofunctor) (f := 𝒱.f) M).hom
        q f₁ f₂ h₁ h₂ =
      (pullModComp f₁ (𝒱.f i₁) q h₁ M).inv ≫ (pullModComp f₂ (𝒱.f i₂) q h₂ M).hom :=
  rfl

/-- **The transition isomorphisms of a restricted descent datum** are those of the datum,
between the composites with the component morphisms of the refinement.

The index type of the refining family and that of the refined family are in INDEPENDENT
universes, which is what an affine-open refinement needs: its index type is `max u v` while
the affine open covering is indexed in `u` and the given family in `v`.  The two are therefore
bound here rather than taken from this section's one-universe `variable` line. -/
theorem rawPullFunctor_obj_hom {T W : Scheme.{u}} {𝒱 : PreZeroHypercover.{w₁} T}
    {𝒳 : PreZeroHypercover.{w₃} W} {k : W ⟶ T} (Φ : 𝒳.HomOver 𝒱 k)
    (E : modulePullbackPseudofunctor.DescentData 𝒱.f) {Y : Scheme.{u}} (q : Y ⟶ W)
    {j₁ j₂ : 𝒳.I₀} (f₁ : Y ⟶ 𝒳.X j₁) (f₂ : Y ⟶ 𝒳.X j₂) (h₁ : f₁ ≫ 𝒳.f j₁ = q)
    (h₂ : f₂ ≫ 𝒳.f j₂ = q) (q' : Y ⟶ T) (hq' : q ≫ k = q')
    (b₁ : Y ⟶ 𝒱.X (Φ.s₀ j₁)) (b₂ : Y ⟶ 𝒱.X (Φ.s₀ j₂))
    (hb₁ : f₁ ≫ Φ.h₀ j₁ = b₁) (hb₂ : f₂ ≫ Φ.h₀ j₂ = b₂)
    (hq₁ : b₁ ≫ 𝒱.f (Φ.s₀ j₁) = q') (hq₂ : b₂ ≫ 𝒱.f (Φ.s₀ j₂) = q') :
    ((Pseudofunctor.DescentData.pullFunctor modulePullbackPseudofunctor
          (f := 𝒱.f) (p := k) (f' := 𝒳.f) (α := Φ.s₀) (p' := Φ.h₀) Φ.w₀).obj E).hom
        q f₁ f₂ h₁ h₂ =
      (pullModComp f₁ (Φ.h₀ j₁) b₁ hb₁ (E.obj (Φ.s₀ j₁))).inv ≫
        E.hom q' b₁ b₂ hq₁ hq₂ ≫
          (pullModComp f₂ (Φ.h₀ j₂) b₂ hb₂ (E.obj (Φ.s₀ j₂))).hom := by
  subst h₁
  exact Pseudofunctor.DescentData.pullFunctorObjHom_eq
    (f := 𝒱.f) (p := k) (f' := 𝒳.f) (α := Φ.s₀) (p' := Φ.h₀) Φ.w₀ E _ f₁ f₂ q' b₁ b₂
    rfl h₂ hq' hb₁ hb₂

/-- **A morphism from a canonical descent datum to a restricted one is compatible with the
transitions of the restricted datum**, read in the `pullHom` spelling: the components, pulled
back to a common test object, are intertwined by the transition of the restricted datum. -/
theorem pullHom_hom_comp_eq {k : W ⟶ T} (Φ : 𝒳.HomOver 𝒱 k)
    (M : modulePullbackPseudofunctor.obj (.mk (op W)))
    (E : modulePullbackPseudofunctor.DescentData 𝒱.f)
    (ε : Pseudofunctor.DescentData.ofObj (F := modulePullbackPseudofunctor) (f := 𝒳.f) M ⟶
      (Pseudofunctor.DescentData.pullFunctor modulePullbackPseudofunctor
        (f := 𝒱.f) (p := k) (f' := 𝒳.f) (α := Φ.s₀) (p' := Φ.h₀) Φ.w₀).obj E)
    {Y : Scheme.{u}} (y : Y ⟶ W) {j₁ j₂ : 𝒳.I₀} (d₁ : Y ⟶ 𝒳.X j₁) (d₂ : Y ⟶ 𝒳.X j₂)
    (hd₁ : d₁ ≫ 𝒳.f j₁ = y) (hd₂ : d₂ ≫ 𝒳.f j₂ = y) (q' : Y ⟶ T) (hq' : y ≫ k = q')
    (b₁ : Y ⟶ 𝒱.X (Φ.s₀ j₁)) (b₂ : Y ⟶ 𝒱.X (Φ.s₀ j₂))
    (hb₁ : d₁ ≫ Φ.h₀ j₁ = b₁) (hb₂ : d₂ ≫ Φ.h₀ j₂ = b₂)
    (hq₁ : b₁ ≫ 𝒱.f (Φ.s₀ j₁) = q') (hq₂ : b₂ ≫ 𝒱.f (Φ.s₀ j₂) = q') :
    pullHom (ε.hom j₁) d₁ y b₁ hd₁ hb₁ ≫ E.hom q' b₁ b₂ hq₁ hq₂ =
      pullHom (ε.hom j₂) d₂ y b₂ hd₂ hb₂ := by
  have hcomm := ε.comm y d₁ d₂ hd₁ hd₂
  have key : ((pullModComp d₁ (𝒳.f j₁) y hd₁ M).inv ≫
        pullHom (ε.hom j₁) d₁ y b₁ hd₁ hb₁ ≫
          (pullModComp d₁ (Φ.h₀ j₁) b₁ hb₁ (E.obj (Φ.s₀ j₁))).hom) ≫
      ((pullModComp d₁ (Φ.h₀ j₁) b₁ hb₁ (E.obj (Φ.s₀ j₁))).inv ≫
        E.hom q' b₁ b₂ hq₁ hq₂ ≫
          (pullModComp d₂ (Φ.h₀ j₂) b₂ hb₂ (E.obj (Φ.s₀ j₂))).hom) =
      ((pullModComp d₁ (𝒳.f j₁) y hd₁ M).inv ≫ (pullModComp d₂ (𝒳.f j₂) y hd₂ M).hom) ≫
        ((pullModComp d₂ (𝒳.f j₂) y hd₂ M).inv ≫
          pullHom (ε.hom j₂) d₂ y b₂ hd₂ hb₂ ≫
            (pullModComp d₂ (Φ.h₀ j₂) b₂ hb₂ (E.obj (Φ.s₀ j₂))).hom) := by
    rw [← map_eq_pullHom' (ε.hom j₁) d₁ y b₁ hd₁ hb₁,
      ← map_eq_pullHom' (ε.hom j₂) d₂ y b₂ hd₂ hb₂,
      ← rawPullFunctor_obj_hom Φ E y d₁ d₂ hd₁ hd₂ q' hq' b₁ b₂ hb₁ hb₂ hq₁ hq₂,
      ← ofObj_hom M y d₁ d₂ hd₁ hd₂]
    exact hcomm
  rw [← cancel_mono (pullModComp d₂ (Φ.h₀ j₂) b₂ hb₂ (E.obj (Φ.s₀ j₂))).hom,
    ← cancel_epi (pullModComp d₁ (𝒳.f j₁) y hd₁ M).inv]
  simp only [Category.assoc, Iso.hom_inv_id_assoc] at key
  simpa only [Category.assoc] using key

end Transitions

/-! ### The local solutions -/

variable {S : Scheme.{u}} (𝒰 : PreZeroHypercover.{v} S)
  (h𝒰 : 𝒰.presieve₀ ∈ Scheme.fpqcPrecoverage.{u} S) (D : QuasicoherentDescentData 𝒰.f)

/-- **The chosen local solution over a member of the affine open covering of the base**: a
quasi-coherent module on `U a` whose canonical descent datum relative to the base change of `𝒰`
to `U a` is isomorphic to the restriction of `D` there.  One is chosen for every `a` at once, so
that the transitions below are transitions between fixed modules. -/
noncomputable def affineOpenModule (a : S.affineCover.I₀) :
    (SheafOfModules.isQuasicoherent (S.affineCover.X a).ringCatSheaf).FullSubcategory :=
  (exists_iso_canonicalDescentFunctor_affineOpen 𝒰 h𝒰 D a).choose

/-- **The chosen isomorphism exhibiting `affineOpenModule` as a local solution.** -/
noncomputable def affineOpenModuleIso (a : S.affineCover.I₀) :
    (canonicalDescentFunctor (𝒰.pullback₁ (S.affineCover.f a)).f).obj
        (affineOpenModule 𝒰 h𝒰 D a) ≅
      (pullFunctor (homOverPullback₁ 𝒰 (S.affineCover.f a))).obj D :=
  (exists_iso_canonicalDescentFunctor_affineOpen 𝒰 h𝒰 D a).choose_spec.some

/-- The chosen isomorphism, read as an isomorphism of the underlying descent data. -/
noncomputable def affineOpenModuleDescentIso (a : S.affineCover.I₀) :
    ((canonicalDescentFunctor (𝒰.pullback₁ (S.affineCover.f a)).f).obj
        (affineOpenModule 𝒰 h𝒰 D a)).obj ≅
      ((pullFunctor (homOverPullback₁ 𝒰 (S.affineCover.f a))).obj D).obj :=
  (ObjectProperty.ι _).mapIso (affineOpenModuleIso 𝒰 h𝒰 D a)

/-- The chosen isomorphism read at the level of the pullback pseudofunctor's descent data, so
that the conversion through the quasi-coherence predicate is performed once and for all. -/
noncomputable def affineOpenRawHom (a : S.affineCover.I₀) :
    Pseudofunctor.DescentData.ofObj (F := modulePullbackPseudofunctor)
        (f := (𝒰.pullback₁ (S.affineCover.f a)).f) (affineOpenModule 𝒰 h𝒰 D a).obj ⟶
      (Pseudofunctor.DescentData.pullFunctor modulePullbackPseudofunctor
          (f := 𝒰.f) (p := S.affineCover.f a) (f' := (𝒰.pullback₁ (S.affineCover.f a)).f)
          (α := (homOverPullback₁ 𝒰 (S.affineCover.f a)).s₀)
          (p' := (homOverPullback₁ 𝒰 (S.affineCover.f a)).h₀)
          (homOverPullback₁ 𝒰 (S.affineCover.f a)).w₀).obj D.obj :=
  (affineOpenModuleDescentIso 𝒰 h𝒰 D a).hom

/-- **The component of the chosen isomorphism above a member of `𝒰`**: an isomorphism between
the pullback of the local solution to `U a ×_S X i` and the pullback of `D i` there. -/
noncomputable def affineOpenComponent (a : S.affineCover.I₀) (i : 𝒰.I₀) :
    pullMod (pullback.fst (S.affineCover.f a) (𝒰.f i)) (affineOpenModule 𝒰 h𝒰 D a).obj ⟶
      pullMod (pullback.snd (S.affineCover.f a) (𝒰.f i)) (D.obj.obj i) :=
  (affineOpenRawHom 𝒰 h𝒰 D a).hom i

/-- The component of the inverse of the chosen isomorphism. -/
noncomputable def affineOpenComponentInv (a : S.affineCover.I₀) (i : 𝒰.I₀) :
    pullMod (pullback.snd (S.affineCover.f a) (𝒰.f i)) (D.obj.obj i) ⟶
      pullMod (pullback.fst (S.affineCover.f a) (𝒰.f i)) (affineOpenModule 𝒰 h𝒰 D a).obj :=
  (affineOpenModuleDescentIso 𝒰 h𝒰 D a).inv.hom i

/-- The two components of the chosen isomorphism are mutually inverse. -/
theorem affineOpenComponent_comp (a : S.affineCover.I₀) (i : 𝒰.I₀) :
    affineOpenComponent 𝒰 h𝒰 D a i ≫ affineOpenComponentInv 𝒰 h𝒰 D a i = 𝟙 _ := by
  have key : ((affineOpenModuleDescentIso 𝒰 h𝒰 D a).hom ≫
      (affineOpenModuleDescentIso 𝒰 h𝒰 D a).inv).hom i = 𝟙 _ := by
    rw [Iso.hom_inv_id]
    exact Pseudofunctor.DescentData.id_hom _ i
  exact key

/-- The two components of the chosen isomorphism are mutually inverse. -/
theorem affineOpenComponentInv_comp (a : S.affineCover.I₀) (i : 𝒰.I₀) :
    affineOpenComponentInv 𝒰 h𝒰 D a i ≫ affineOpenComponent 𝒰 h𝒰 D a i = 𝟙 _ := by
  have key : ((affineOpenModuleDescentIso 𝒰 h𝒰 D a).inv ≫
      (affineOpenModuleDescentIso 𝒰 h𝒰 D a).hom).hom i = 𝟙 _ := by
    rw [Iso.inv_hom_id]
    exact Pseudofunctor.DescentData.id_hom _ i
  exact key

/-- **The comparison over a scheme mapping to an affine open of the base and to a member of the
family**, compatibly: the local solution over that affine open, pulled back, is the component of
`D` there, pulled back. -/
noncomputable def localComparison (a : S.affineCover.I₀) (i : 𝒰.I₀) {V : Scheme.{u}}
    (g : V ⟶ S.affineCover.X a) (c : V ⟶ 𝒰.X i)
    (h : g ≫ S.affineCover.f a = c ≫ 𝒰.f i) :
    pullMod g (affineOpenModule 𝒰 h𝒰 D a).obj ⟶ pullMod c (D.obj.obj i) :=
  pullHom (affineOpenComponent 𝒰 h𝒰 D a i) (pullback.lift g c h) g c
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)

/-- The inverse comparison, written out rather than as an inverse, so that it is compatible with
further pullback on the nose. -/
noncomputable def localComparisonInv (a : S.affineCover.I₀) (i : 𝒰.I₀) {V : Scheme.{u}}
    (g : V ⟶ S.affineCover.X a) (c : V ⟶ 𝒰.X i)
    (h : g ≫ S.affineCover.f a = c ≫ 𝒰.f i) :
    pullMod c (D.obj.obj i) ⟶ pullMod g (affineOpenModule 𝒰 h𝒰 D a).obj :=
  pullHom (affineOpenComponentInv 𝒰 h𝒰 D a i) (pullback.lift g c h) c g
    (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)

/-- A morphism into a pullback with the given projections is the induced lift. -/
private theorem eq_pullback_lift {X Y Z V : Scheme.{u}} {f : X ⟶ Z} {g : Y ⟶ Z}
    (k : V ⟶ pullback f g) (a : V ⟶ X) (b : V ⟶ Y) (h : a ≫ f = b ≫ g)
    (hk₁ : k ≫ pullback.fst f g = a) (hk₂ : k ≫ pullback.snd f g = b) :
    k = pullback.lift a b h :=
  pullback.hom_ext (by rw [pullback.lift_fst]; exact hk₁) (by rw [pullback.lift_snd]; exact hk₂)

/-- **The comparison may be read along any factorization through the fibre product**, not only
along the canonical lift; the factorization is unique, the fibre product being a limit. -/
theorem localComparison_eq (a : S.affineCover.I₀) (i : 𝒰.I₀) {V : Scheme.{u}}
    (g : V ⟶ S.affineCover.X a) (c : V ⟶ 𝒰.X i)
    (h : g ≫ S.affineCover.f a = c ≫ 𝒰.f i)
    (k : V ⟶ pullback (S.affineCover.f a) (𝒰.f i))
    (hk₁ : k ≫ pullback.fst (S.affineCover.f a) (𝒰.f i) = g)
    (hk₂ : k ≫ pullback.snd (S.affineCover.f a) (𝒰.f i) = c) :
    localComparison 𝒰 h𝒰 D a i g c h =
      pullHom (affineOpenComponent 𝒰 h𝒰 D a i) k g c hk₁ hk₂ :=
  (pullHom_congr_mor (affineOpenComponent 𝒰 h𝒰 D a i)
    (eq_pullback_lift k g c h hk₁ hk₂)
    g c hk₁ hk₂ (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)).symm

/-- **The inverse comparison may be read along any factorization through the fibre product.** -/
theorem localComparisonInv_eq (a : S.affineCover.I₀) (i : 𝒰.I₀) {V : Scheme.{u}}
    (g : V ⟶ S.affineCover.X a) (c : V ⟶ 𝒰.X i)
    (h : g ≫ S.affineCover.f a = c ≫ 𝒰.f i)
    (k : V ⟶ pullback (S.affineCover.f a) (𝒰.f i))
    (hk₁ : k ≫ pullback.fst (S.affineCover.f a) (𝒰.f i) = g)
    (hk₂ : k ≫ pullback.snd (S.affineCover.f a) (𝒰.f i) = c) :
    localComparisonInv 𝒰 h𝒰 D a i g c h =
      pullHom (affineOpenComponentInv 𝒰 h𝒰 D a i) k c g hk₂ hk₁ :=
  (pullHom_congr_mor (affineOpenComponentInv 𝒰 h𝒰 D a i)
    (eq_pullback_lift k g c h hk₁ hk₂)
    c g hk₂ hk₁ (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)).symm

/-- The comparison and the inverse comparison are mutually inverse. -/
theorem localComparison_comp_inv (a : S.affineCover.I₀) (i : 𝒰.I₀) {V : Scheme.{u}}
    (g : V ⟶ S.affineCover.X a) (c : V ⟶ 𝒰.X i)
    (h : g ≫ S.affineCover.f a = c ≫ 𝒰.f i) :
    localComparison 𝒰 h𝒰 D a i g c h ≫ localComparisonInv 𝒰 h𝒰 D a i g c h = 𝟙 _ := by
  rw [localComparison_eq 𝒰 h𝒰 D a i g c h (pullback.lift g c h)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _),
    localComparisonInv_eq 𝒰 h𝒰 D a i g c h (pullback.lift g c h)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _),
    ← pullHom_comp (affineOpenComponent 𝒰 h𝒰 D a i) (affineOpenComponentInv 𝒰 h𝒰 D a i)
      (pullback.lift g c h) g c g (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _)
      (pullback.lift_fst _ _ _),
    affineOpenComponent_comp]
  exact pullHom_one _ _ _

/-- The comparison and the inverse comparison are mutually inverse. -/
theorem localComparisonInv_comp (a : S.affineCover.I₀) (i : 𝒰.I₀) {V : Scheme.{u}}
    (g : V ⟶ S.affineCover.X a) (c : V ⟶ 𝒰.X i)
    (h : g ≫ S.affineCover.f a = c ≫ 𝒰.f i) :
    localComparisonInv 𝒰 h𝒰 D a i g c h ≫ localComparison 𝒰 h𝒰 D a i g c h = 𝟙 _ := by
  rw [localComparison_eq 𝒰 h𝒰 D a i g c h (pullback.lift g c h)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _),
    localComparisonInv_eq 𝒰 h𝒰 D a i g c h (pullback.lift g c h)
      (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _),
    ← pullHom_comp (affineOpenComponentInv 𝒰 h𝒰 D a i) (affineOpenComponent 𝒰 h𝒰 D a i)
      (pullback.lift g c h) c g c (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _)
      (pullback.lift_snd _ _ _),
    affineOpenComponentInv_comp]
  exact pullHom_one _ _ _

/-- **The comparison is compatible with pullback**: restricting it along a morphism of the test
object gives the comparison at the composites. -/
theorem pullHom_localComparison (a : S.affineCover.I₀) (i : 𝒰.I₀) {V : Scheme.{u}}
    (g : V ⟶ S.affineCover.X a) (c : V ⟶ 𝒰.X i)
    (h : g ≫ S.affineCover.f a = c ≫ 𝒰.f i) {V' : Scheme.{u}} (m : V' ⟶ V)
    (g' : V' ⟶ S.affineCover.X a) (c' : V' ⟶ 𝒰.X i) (hg : m ≫ g = g') (hc : m ≫ c = c')
    (h' : g' ≫ S.affineCover.f a = c' ≫ 𝒰.f i) :
    pullHom (localComparison 𝒰 h𝒰 D a i g c h) m g' c' hg hc =
      localComparison 𝒰 h𝒰 D a i g' c' h' := by
  rw [localComparison_eq 𝒰 h𝒰 D a i g' c' h' (m ≫ pullback.lift g c h)
      (by rw [Category.assoc, pullback.lift_fst, hg])
      (by rw [Category.assoc, pullback.lift_snd, hc])]
  exact pullHom_pullHom (affineOpenComponent 𝒰 h𝒰 D a i) (pullback.lift g c h) g c m g' c'
    (pullback.lift_fst _ _ _) (pullback.lift_snd _ _ _) hg hc

/-- **The inverse comparison is compatible with pullback.** -/
theorem pullHom_localComparisonInv (a : S.affineCover.I₀) (i : 𝒰.I₀) {V : Scheme.{u}}
    (g : V ⟶ S.affineCover.X a) (c : V ⟶ 𝒰.X i)
    (h : g ≫ S.affineCover.f a = c ≫ 𝒰.f i) {V' : Scheme.{u}} (m : V' ⟶ V)
    (g' : V' ⟶ S.affineCover.X a) (c' : V' ⟶ 𝒰.X i) (hg : m ≫ g = g') (hc : m ≫ c = c')
    (h' : g' ≫ S.affineCover.f a = c' ≫ 𝒰.f i) :
    pullHom (localComparisonInv 𝒰 h𝒰 D a i g c h) m c' g' hc hg =
      localComparisonInv 𝒰 h𝒰 D a i g' c' h' := by
  rw [localComparisonInv_eq 𝒰 h𝒰 D a i g' c' h' (m ≫ pullback.lift g c h)
      (by rw [Category.assoc, pullback.lift_fst, hg])
      (by rw [Category.assoc, pullback.lift_snd, hc])]
  exact pullHom_pullHom (affineOpenComponentInv 𝒰 h𝒰 D a i) (pullback.lift g c h) c g m c' g'
    (pullback.lift_snd _ _ _) (pullback.lift_fst _ _ _) hc hg

/-- **The local comparisons are compatible with the transitions of `D`.** -/
theorem localComparison_comp_hom (a : S.affineCover.I₀) {V : Scheme.{u}}
    (g : V ⟶ S.affineCover.X a) (q : V ⟶ S) (hq : g ≫ S.affineCover.f a = q)
    (i₁ i₂ : 𝒰.I₀) (c₁ : V ⟶ 𝒰.X i₁) (c₂ : V ⟶ 𝒰.X i₂)
    (hc₁ : c₁ ≫ 𝒰.f i₁ = q) (hc₂ : c₂ ≫ 𝒰.f i₂ = q)
    (h₁ : g ≫ S.affineCover.f a = c₁ ≫ 𝒰.f i₁) (h₂ : g ≫ S.affineCover.f a = c₂ ≫ 𝒰.f i₂) :
    localComparison 𝒰 h𝒰 D a i₁ g c₁ h₁ ≫ D.obj.hom q c₁ c₂ hc₁ hc₂ =
      localComparison 𝒰 h𝒰 D a i₂ g c₂ h₂ :=
  pullHom_hom_comp_eq (homOverPullback₁ 𝒰 (S.affineCover.f a))
    (affineOpenModule 𝒰 h𝒰 D a).obj D.obj (affineOpenRawHom 𝒰 h𝒰 D a) g
    (pullback.lift g c₁ h₁) (pullback.lift g c₂ h₂)
    (pullback.lift_fst _ _ _) (pullback.lift_fst _ _ _) q hq c₁ c₂
    (pullback.lift_snd _ _ _) (pullback.lift_snd _ _ _) hc₁ hc₂

/-! ### The glued transitions -/

/-- **The transition between two local solutions**, read off a common test object lying over a
member of the family. -/
noncomputable def localTransition (a b : S.affineCover.I₀) {V : Scheme.{u}}
    (g₁ : V ⟶ S.affineCover.X a) (g₂ : V ⟶ S.affineCover.X b) (i : 𝒰.I₀) (c : V ⟶ 𝒰.X i)
    (h₁ : g₁ ≫ S.affineCover.f a = c ≫ 𝒰.f i)
    (h₂ : g₂ ≫ S.affineCover.f b = c ≫ 𝒰.f i) :
    pullMod g₁ (affineOpenModule 𝒰 h𝒰 D a).obj ⟶
      pullMod g₂ (affineOpenModule 𝒰 h𝒰 D b).obj :=
  localComparison 𝒰 h𝒰 D a i g₁ c h₁ ≫ localComparisonInv 𝒰 h𝒰 D b i g₂ c h₂

/-- **The transition does not depend on the member of the family it is read off.**  The two
candidate transitions differ by the transition of `D` between the two members, inserted once on
each side of the comparison, and it cancels.  This is the cocycle condition of the datum being
built: the three transitions appearing in it may all be read off one member of the family, where
they compose because the comparisons are isomorphisms. -/
theorem localTransition_eq (a b : S.affineCover.I₀) {V : Scheme.{u}} (q : V ⟶ S)
    (g₁ : V ⟶ S.affineCover.X a) (g₂ : V ⟶ S.affineCover.X b)
    (hg₁ : g₁ ≫ S.affineCover.f a = q) (hg₂ : g₂ ≫ S.affineCover.f b = q)
    (i₁ : 𝒰.I₀) (c₁ : V ⟶ 𝒰.X i₁) (hc₁ : c₁ ≫ 𝒰.f i₁ = q)
    (i₂ : 𝒰.I₀) (c₂ : V ⟶ 𝒰.X i₂) (hc₂ : c₂ ≫ 𝒰.f i₂ = q)
    (ha₁ : g₁ ≫ S.affineCover.f a = c₁ ≫ 𝒰.f i₁)
    (hb₁ : g₂ ≫ S.affineCover.f b = c₁ ≫ 𝒰.f i₁)
    (ha₂ : g₁ ≫ S.affineCover.f a = c₂ ≫ 𝒰.f i₂)
    (hb₂ : g₂ ≫ S.affineCover.f b = c₂ ≫ 𝒰.f i₂) :
    localTransition 𝒰 h𝒰 D a b g₁ g₂ i₁ c₁ ha₁ hb₁ =
      localTransition 𝒰 h𝒰 D a b g₁ g₂ i₂ c₂ ha₂ hb₂ := by
  have hA := localComparison_comp_hom 𝒰 h𝒰 D a g₁ q hg₁ i₁ i₂ c₁ c₂ hc₁ hc₂ ha₁ ha₂
  have hB := localComparison_comp_hom 𝒰 h𝒰 D b g₂ q hg₂ i₁ i₂ c₁ c₂ hc₁ hc₂ hb₁ hb₂
  have hiso : IsIso (localComparison 𝒰 h𝒰 D b i₁ g₂ c₁ hb₁) :=
    ⟨localComparisonInv 𝒰 h𝒰 D b i₁ g₂ c₁ hb₁,
      localComparison_comp_inv 𝒰 h𝒰 D b i₁ g₂ c₁ hb₁,
      localComparisonInv_comp 𝒰 h𝒰 D b i₁ g₂ c₁ hb₁⟩
  have hinv : localComparisonInv 𝒰 h𝒰 D b i₁ g₂ c₁ hb₁ =
      D.obj.hom q c₁ c₂ hc₁ hc₂ ≫ localComparisonInv 𝒰 h𝒰 D b i₂ g₂ c₂ hb₂ := by
    rw [← cancel_epi (localComparison 𝒰 h𝒰 D b i₁ g₂ c₁ hb₁),
      localComparison_comp_inv, ← Category.assoc, hB, localComparison_comp_inv]
  change localComparison 𝒰 h𝒰 D a i₁ g₁ c₁ ha₁ ≫ localComparisonInv 𝒰 h𝒰 D b i₁ g₂ c₁ hb₁ =
    localComparison 𝒰 h𝒰 D a i₂ g₁ c₂ ha₂ ≫ localComparisonInv 𝒰 h𝒰 D b i₂ g₂ c₂ hb₂
  rw [hinv, ← hA, Category.assoc]

/-- **The transition is compatible with pullback.** -/
theorem pullHom_localTransition (a b : S.affineCover.I₀) {V : Scheme.{u}}
    (g₁ : V ⟶ S.affineCover.X a) (g₂ : V ⟶ S.affineCover.X b) (i : 𝒰.I₀) (c : V ⟶ 𝒰.X i)
    (h₁ : g₁ ≫ S.affineCover.f a = c ≫ 𝒰.f i) (h₂ : g₂ ≫ S.affineCover.f b = c ≫ 𝒰.f i)
    {V' : Scheme.{u}} (m : V' ⟶ V) (g₁' : V' ⟶ S.affineCover.X a)
    (g₂' : V' ⟶ S.affineCover.X b) (c' : V' ⟶ 𝒰.X i) (hm₁ : m ≫ g₁ = g₁') (hm₂ : m ≫ g₂ = g₂')
    (hmc : m ≫ c = c') (h₁' : g₁' ≫ S.affineCover.f a = c' ≫ 𝒰.f i)
    (h₂' : g₂' ≫ S.affineCover.f b = c' ≫ 𝒰.f i) :
    pullHom (localTransition 𝒰 h𝒰 D a b g₁ g₂ i c h₁ h₂) m g₁' g₂' hm₁ hm₂ =
      localTransition 𝒰 h𝒰 D a b g₁' g₂' i c' h₁' h₂' := by
  change pullHom (localComparison 𝒰 h𝒰 D a i g₁ c h₁ ≫
      localComparisonInv 𝒰 h𝒰 D b i g₂ c h₂) m g₁' g₂' hm₁ hm₂ =
    localComparison 𝒰 h𝒰 D a i g₁' c' h₁' ≫ localComparisonInv 𝒰 h𝒰 D b i g₂' c' h₂'
  rw [pullHom_comp (localComparison 𝒰 h𝒰 D a i g₁ c h₁)
      (localComparisonInv 𝒰 h𝒰 D b i g₂ c h₂) m g₁' c' g₂' hm₁ hmc hm₂,
    pullHom_localComparison 𝒰 h𝒰 D a i g₁ c h₁ m g₁' c' hm₁ hmc h₁',
    pullHom_localComparisonInv 𝒰 h𝒰 D b i g₂ c h₂ m g₂' c' hm₂ hmc h₂']

/-- **The transition at a repeated member of the affine open covering is the identity**, which is
the `hom_self` condition of the datum being built. -/
theorem localTransition_self (a : S.affineCover.I₀) {V : Scheme.{u}}
    (g : V ⟶ S.affineCover.X a) (i : 𝒰.I₀) (c : V ⟶ 𝒰.X i)
    (h : g ≫ S.affineCover.f a = c ≫ 𝒰.f i) :
    localTransition 𝒰 h𝒰 D a a g g i c h h = 𝟙 _ :=
  localComparison_comp_inv 𝒰 h𝒰 D a i g c h

/-- **The transitions read off one member of the family compose**, which is the `hom_comp`
condition of the datum being built; together with `localTransition_eq`, which makes the member
irrelevant, it is the cocycle condition. -/
theorem localTransition_comp (a b d : S.affineCover.I₀) {V : Scheme.{u}}
    (g₁ : V ⟶ S.affineCover.X a) (g₂ : V ⟶ S.affineCover.X b) (g₃ : V ⟶ S.affineCover.X d)
    (i : 𝒰.I₀) (c : V ⟶ 𝒰.X i) (h₁ : g₁ ≫ S.affineCover.f a = c ≫ 𝒰.f i)
    (h₂ : g₂ ≫ S.affineCover.f b = c ≫ 𝒰.f i) (h₃ : g₃ ≫ S.affineCover.f d = c ≫ 𝒰.f i) :
    localTransition 𝒰 h𝒰 D a b g₁ g₂ i c h₁ h₂ ≫ localTransition 𝒰 h𝒰 D b d g₂ g₃ i c h₂ h₃ =
      localTransition 𝒰 h𝒰 D a d g₁ g₃ i c h₁ h₃ := by
  change (localComparison 𝒰 h𝒰 D a i g₁ c h₁ ≫ localComparisonInv 𝒰 h𝒰 D b i g₂ c h₂) ≫
      localComparison 𝒰 h𝒰 D b i g₂ c h₂ ≫ localComparisonInv 𝒰 h𝒰 D d i g₃ c h₃ =
    localComparison 𝒰 h𝒰 D a i g₁ c h₁ ≫ localComparisonInv 𝒰 h𝒰 D d i g₃ c h₃
  rw [Category.assoc, ← Category.assoc (localComparisonInv 𝒰 h𝒰 D b i g₂ c h₂),
    localComparisonInv_comp, Category.id_comp]

end QuasicoherentDescentData

end AlgebraicGeometry

end
