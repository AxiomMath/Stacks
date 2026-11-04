module

public import StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFpqcDescent
public import Mathlib.AlgebraicGeometry.Morphisms.Flat
public import Mathlib.AlgebraicGeometry.PullbackCarrier
public import StacksFrontier.AlgebraicGeometry.FormalScheme.FormalSpectrumFpqcSheaf
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Further results on `StacksFrontier.AlgebraicGeometry.FormalScheme.FunctorOfPointsFpqcDescent`

Further results on fpqc descent for the functor of points of a formal scheme.

## Main results

* `AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints_of_isoSpf`: the functor of points
  of a formal scheme isomorphic to a formal spectrum is an fpqc sheaf.
* `AlgebraicGeometry.exists_comp_eq_of_flat_surjective`: a point of a formal scheme over `T'`
  whose two pullbacks to `T' ×_T T'` agree descends along a flat, surjective, quasi-compact
  morphism `T' ⟶ T`.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite TopologicalRing

universe u

namespace CategoryTheory.Presieve

variable {C : Type*} [Category* C] {P : Cᵒᵖ ⥤ Type*}

end CategoryTheory.Presieve

namespace AlgebraicGeometry

section Spf

variable (A : Type u) [CommRing A] [TopologicalSpace A] [IsTopologicalRing A]

variable [IsLinearTopology A A]

/-- **Stacks 0AI2**, the gluing clause included, for an affine formal scheme: the functor of
points of a formal scheme isomorphic to a formal spectrum is an fpqc sheaf.

Transporting along the isomorphism reduces this to
`AlgebraicGeometry.isSheaf_fpqcTopology_formalSchemePoints_spfFormalScheme`. -/
@[stacks 0AI2 "sheaf condition with gluing, for a formal scheme isomorphic to a formal spectrum"]
theorem isSheaf_fpqcTopology_formalSchemePoints_of_isoSpf {X : FormalScheme.{u}}
    (hA : IsAdmissible A) (e : X ≅ spfFormalScheme A hA) :
    Presieve.IsSheaf Scheme.fpqcTopology.{u} (formalSchemePoints X) :=
  Presieve.isSheaf_iso _ (formalSchemePointsFunctor.mapIso e).symm
    (isSheaf_fpqcTopology_formalSchemePoints_spfFormalScheme A hA)

end Spf

/-! ### The inclusion of an open subspace is a monomorphism -/

/-- Morphisms into an open subspace of a locally topologically ringed space are determined by
their composites with the inclusion of that subspace: the inclusion of an open subspace is a
monomorphism of presheafed spaces. -/
@[ega "I 10.2.3" "more general"]
theorem ofRestrict_hom_ext {Z X : LTRS.{u}} (V : Opens X) {a b : Z ⟶ X.restrict V}
    (h : a ≫ X.ofRestrict V = b ≫ X.ofRestrict V) : a = b := by
  refine LocallyTopologicallyRingedSpace.Hom.ext' ?_
  have h' : ((a ≫ X.ofRestrict V).toHom : Z.toPresheafedSpace ⟶ X.toPresheafedSpace)
      = ((b ≫ X.ofRestrict V).toHom : Z.toPresheafedSpace ⟶ X.toPresheafedSpace) :=
    congrArg LocallyTopologicallyRingedSpace.Hom.toHom h
  rw [LocallyTopologicallyRingedSpace.comp_toHom,
    LocallyTopologicallyRingedSpace.comp_toHom] at h'
  exact (cancel_mono _).1 h'

/-- Morphisms into a space isomorphic to an open subspace of `𝔛` are determined by their
composites into `𝔛`. This is `AlgebraicGeometry.ofRestrict_hom_ext` read through an
isomorphism, the form in which an affine formal chart `𝔛|_𝔘 ≅ Spf A` supplies it. -/
theorem isoRestrict_hom_ext {Z W X : LTRS.{u}} (V : Opens X) (χ : W ≅ X.restrict V)
    {a b : Z ⟶ W} (h : a ≫ (χ.hom ≫ X.ofRestrict V) = b ≫ (χ.hom ≫ X.ofRestrict V)) :
    a = b := by
  refine (Iso.cancel_iso_hom_right a b χ).1 (ofRestrict_hom_ext V ?_)
  rw [Category.assoc, Category.assoc]
  exact h

/-! ### Descent of a point along a faithfully flat morphism -/

/-- The local step of `AlgebraicGeometry.exists_comp_eq_of_flat_surjective`: if `f` maps the
preimage `p⁻¹(W)` of an open `W` of `T` into an affine formal chart `𝔛|_𝔘 ≅ Spf A`, then the
restriction of `f` to `T' ×_T W` descends to a point of `𝔛` over `W`. -/
theorem exists_comp_eq_pullback_snd_of_isoSpf (X : FormalScheme.{u}) {T T' : Scheme.{u}}
    (p : T' ⟶ T) [Flat p] [Surjective p] [QuasiCompact p]
    (f : schemeToFormalScheme.obj T' ⟶ X)
    (hcompat : ∀ {Z : Scheme.{u}} (q₁ q₂ : Z ⟶ T'), q₁ ≫ p = q₂ ≫ p →
      schemeToFormalScheme.map q₁ ≫ f = schemeToFormalScheme.map q₂ ≫ f)
    (W : T.Opens) (U : Opens X.obj) (A : Type u) [CommRing A] [TopologicalSpace A]
    [IsTopologicalRing A] [IsLinearTopology A A] (hA : IsAdmissible A)
    (e : X.obj.toPresheafedSpace.restrict (f := U.inclusion') U.isOpenEmbedding' ≅ Spf A)
    (hW : ∀ w : ↥T', p.base w ∈ W → f.hom.toHom.base w ∈ U) :
    ∃ s : schemeToFormalScheme.obj W.toScheme ⟶ X,
      schemeToFormalScheme.map (pullback.fst p W.ι) ≫ f
        = schemeToFormalScheme.map (pullback.snd p W.ι) ≫ s := by
  set χ : X.obj.restrict U ≅ spfLTRS A hA.1 := ltrsIsoOfPresheafedSpaceIso e
  set a : pullback p W.ι ⟶ T' := pullback.fst p W.ι
  set b : pullback p W.ι ⟶ W.toScheme := pullback.snd p W.ι
  have hab : a ≫ p = b ≫ W.ι := pullback.condition
  have hrange : Set.range (schemeToFormalScheme.map a ≫ f).hom.toHom.base
      ⊆ Set.range (X.obj.ofRestrict U).toHom.base := by
    rintro _ ⟨q, rfl⟩
    have h₁ : p.base (a.base q) = W.ι.base (b.base q) :=
      congrArg (fun m : pullback p W.ι ⟶ T => m.base q) hab
    exact ⟨⟨f.hom.toHom.base (a.base q), hW _ (h₁ ▸ (b.base q).2 : p.base (a.base q) ∈ W)⟩, rfl⟩
  set ι₀ : spfFormalScheme A hA ⟶ X := ObjectProperty.homMk (χ.inv ≫ X.obj.ofRestrict U)
  set pt : schemeToFormalScheme.obj (pullback p W.ι) ⟶ spfFormalScheme A hA :=
    ObjectProperty.homMk (liftToRestrict U (schemeToFormalScheme.map a ≫ f).hom hrange ≫ χ.hom)
  have hptι : pt ≫ ι₀ = schemeToFormalScheme.map a ≫ f := by
    refine InducedCategory.hom_ext ?_
    show (liftToRestrict U (schemeToFormalScheme.map a ≫ f).hom hrange ≫ χ.hom)
        ≫ (χ.inv ≫ X.obj.ofRestrict U) = (schemeToFormalScheme.map a ≫ f).hom
    rw [Category.assoc, Iso.hom_inv_id_assoc]
    exact liftToRestrict_comp_ofRestrict U _ hrange
  have hptcompat : ∀ {Z : Scheme.{u}} (q₁ q₂ : Z ⟶ pullback p W.ι), q₁ ≫ b = q₂ ≫ b →
      schemeToFormalScheme.map q₁ ≫ pt = schemeToFormalScheme.map q₂ ≫ pt := by
    intro Z q₁ q₂ hq
    have h₂ : (schemeToFormalScheme.map q₁ ≫ pt) ≫ ι₀
        = (schemeToFormalScheme.map q₂ ≫ pt) ≫ ι₀ := by
      rw [Category.assoc, Category.assoc, hptι, ← Functor.map_comp_assoc,
        ← Functor.map_comp_assoc]
      exact hcompat _ _ (by rw [Category.assoc, Category.assoc, hab, reassoc_of% hq])
    exact InducedCategory.hom_ext
      (isoRestrict_hom_ext U χ.symm (congrArg InducedCategory.Hom.hom h₂))
  obtain ⟨s, hs, -⟩ := Presieve.isSheafFor_singleton.1
    ((Presieve.isSheafFor_iff_generate (Presieve.singleton b)).2
      (isSheaf_fpqcTopology_formalSchemePoints_spfFormalScheme A hA _
        (Scheme.Hom.generate_singleton_mem_propQCTopology (P := @Flat) b inferInstance)))
    pt fun {_} q₁ q₂ hq => hptcompat q₁ q₂ hq
  have hsb : schemeToFormalScheme.map b ≫ s = pt := hs
  exact ⟨s ≫ ι₀, hptι.symm.trans
    ((congrArg (fun m : schemeToFormalScheme.obj (pullback p W.ι) ⟶
        spfFormalScheme A hA => m ≫ ι₀) hsb).symm.trans (Category.assoc _ _ _))⟩

/-- The gluing step of `AlgebraicGeometry.exists_comp_eq_of_flat_surjective`: for a flat surjective
`p : T' ⟶ T`, if the restriction of `f` descends over every member of an open cover of `T`, then
`f` descends to a point of `𝔛` over `T`. -/
theorem exists_comp_eq_of_opensCover_of_flat (X : FormalScheme.{u}) {T T' : Scheme.{u}}
    (p : T' ⟶ T) [Flat p] [Surjective p] (f : schemeToFormalScheme.obj T' ⟶ X) {ι : Type*}
    (V : ι → T.Opens) (hV : iSup V = ⊤)
    (s : ∀ i, schemeToFormalScheme.obj (V i).toScheme ⟶ X)
    (hs : ∀ i, schemeToFormalScheme.map (pullback.fst p (V i).ι) ≫ f
      = schemeToFormalScheme.map (pullback.snd p (V i).ι) ≫ s i) :
    ∃ t : schemeToFormalScheme.obj T ⟶ X, schemeToFormalScheme.map p ≫ t = f := by
  -- Reading a local descent off on any pair of legs over `T` and `V z`.
  have hkey : ∀ (z : ι) (Z : Scheme.{u}) (u : Z ⟶ T') (w : Z ⟶ (V z).toScheme),
      u ≫ p = w ≫ (V z).ι →
      schemeToFormalScheme.map w ≫ s z = schemeToFormalScheme.map u ≫ f := by
    intro z Z u w hcomm
    rw [← pullback.lift_snd u w hcomm, Functor.map_comp_assoc, ← hs z,
      ← Functor.map_comp_assoc, pullback.lift_fst]
  -- The local descents agree on the overlaps.
  have hcompatV : Presieve.Arrows.Compatible (formalSchemePoints X)
      (fun z : ι => (V z).ι) s := by
    intro z₁ z₂ Z g₁ g₂ hg
    have hcond : pullback.fst p (g₁ ≫ (V z₁).ι) ≫ p
        = pullback.snd p (g₁ ≫ (V z₁).ι) ≫ (g₁ ≫ (V z₁).ι) := pullback.condition
    show schemeToFormalScheme.map g₁ ≫ s z₁ = schemeToFormalScheme.map g₂ ≫ s z₂
    refine formalSchemeHom_ext_of_flat_of_jointlySurjective
      (V := fun _ : Unit => pullback p (g₁ ≫ (V z₁).ι))
      (fun _ => pullback.snd p (g₁ ≫ (V z₁).ι)) (fun _ => inferInstance)
      (fun y => ⟨⟨⟩, (pullback.snd p (g₁ ≫ (V z₁).ι)).surjective y⟩) fun _ => ?_
    rw [← Functor.map_comp_assoc, ← Functor.map_comp_assoc]
    exact (hkey z₁ _ _ _ (by rw [hcond, Category.assoc])).trans
      (hkey z₂ _ _ _ (by rw [hcond, Category.assoc, hg])).symm
  -- Glue, the functor of points being a Zariski sheaf.
  obtain ⟨t, ht, -⟩ := (Presieve.isSheafFor_arrows_iff _ _).1
    (isSheafFor_opensCover_formalSchemePoints X V hV) s hcompatV
  refine ⟨t, ?_⟩
  refine formalSchemeHom_ext_of_flat_of_jointlySurjective
    (V := fun z : ι => pullback p (V z).ι)
    (fun z => pullback.fst p (V z).ι) (fun _ => inferInstance) (fun y => ?_) fun z => ?_
  · obtain ⟨i, hi⟩ := Opens.mem_iSup.1 (by rw [hV]; trivial : p.base y ∈ iSup V)
    obtain ⟨q, hq, -⟩ := Scheme.Pullback.exists_preimage_pullback (f := p) (g := (V i).ι)
      y ⟨p.base y, hi⟩ rfl
    exact ⟨i, q, hq⟩
  · have ht' : schemeToFormalScheme.map (V z).ι ≫ t = s z := ht z
    calc schemeToFormalScheme.map (pullback.fst p (V z).ι) ≫ (schemeToFormalScheme.map p ≫ t)
        = schemeToFormalScheme.map (pullback.fst p (V z).ι ≫ p) ≫ t :=
          (Functor.map_comp_assoc _ _ _ _).symm
      _ = schemeToFormalScheme.map (pullback.snd p (V z).ι ≫ (V z).ι) ≫ t := by
          rw [pullback.condition]
      _ = schemeToFormalScheme.map (pullback.snd p (V z).ι)
            ≫ (schemeToFormalScheme.map (V z).ι ≫ t) := Functor.map_comp_assoc _ _ _ _
      _ = schemeToFormalScheme.map (pullback.snd p (V z).ι) ≫ s z := by rw [ht']
      _ = schemeToFormalScheme.map (pullback.fst p (V z).ι) ≫ f := (hs z).symm

/-- **Stacks 0AI2**, the descent the reduction of the fpqc sheaf condition asks for. Let
`p : T' ⟶ T` be a flat, surjective, quasi-compact morphism of schemes and let `f : T' ⟶ 𝔛` be a
point of a formal scheme whose two pullbacks to `T' ×_T T'` agree — in the form used here, which
pulls back to the same point along any pair of morphisms into `T'` equalized by `p`. Then `f` is
the pullback of a point of `𝔛` over `T`.

The underlying continuous map descends because `p` is a quotient map and `f` is constant on its
fibres. Over an open of `T` on which the descended map stays inside one affine formal chart
`𝔛|_𝔘 ≅ Spf A`, the restriction of `f` descends because `h_{Spf A}` is already known to be an
fpqc sheaf; such opens cover `T`, and the local descents glue because `h_𝔛` is a Zariski sheaf
and is separated for the fpqc topology. -/
theorem exists_comp_eq_of_flat_surjective (X : FormalScheme.{u}) {T T' : Scheme.{u}} (p : T' ⟶ T)
    [Flat p] [Surjective p] [QuasiCompact p] (f : schemeToFormalScheme.obj T' ⟶ X)
    (hcompat : ∀ {Z : Scheme.{u}} (q₁ q₂ : Z ⟶ T'), q₁ ≫ p = q₂ ≫ p →
      schemeToFormalScheme.map q₁ ≫ f = schemeToFormalScheme.map q₂ ≫ f) :
    ∃ t : schemeToFormalScheme.obj T ⟶ X, schemeToFormalScheme.map p ≫ t = f := by
  classical
  choose U hxU A hlin hadm hiso using X.property
  -- `f` is constant on the fibres of `p`, because `T' ×_T T'` surjects onto the kernel pair.
  have hfib : ∀ a b : T', p.base a = p.base b →
      f.hom.toHom.base a = f.hom.toHom.base b := by
    intro a b hab
    obtain ⟨c, rfl, rfl⟩ := Scheme.Pullback.exists_preimage_pullback a b hab
    exact congrArg (fun m : schemeToFormalScheme.obj (pullback p p) ⟶ X => m.hom.toHom.base c)
      (hcompat (pullback.fst p p) (pullback.snd p p) pullback.condition)
  have hquot : Topology.IsQuotientMap (⇑p) := Flat.isQuotientMap_of_surjective p
  -- The points of `T` all of whose `p`-preimages are sent into a given open form an open set.
  have hopen : ∀ x : ↥X.obj, IsOpen {y : ↥T |
      ∀ w : ↥T', p.base w = y → f.hom.toHom.base w ∈ U x} := by
    intro x
    rw [← hquot.isOpen_preimage]
    have hset : (⇑p) ⁻¹' {y : ↥T | ∀ w : ↥T', p.base w = y → f.hom.toHom.base w ∈ U x}
        = (⇑f.hom.toHom.base) ⁻¹' (U x : Set ↥X.obj) := by
      refine Set.ext fun z => ⟨fun hz => hz z rfl, fun hz w hw => ?_⟩
      rw [hfib w z hw]
      exact hz
    rw [hset]
    exact ((Opens.map f.hom.toHom.base).obj (U x)).isOpen
  -- The covering family of `T`, indexed by the points of `T'`.
  set V : ↥T' → T.Opens := fun z =>
    ⟨{y : ↥T | ∀ w : ↥T', p.base w = y → f.hom.toHom.base w ∈ U (f.hom.toHom.base z)},
      hopen _⟩
  have hVmem : ∀ z : ↥T', p.base z ∈ V z := by
    intro z w hw
    rw [hfib w z hw]
    exact hxU _
  have hVcover : iSup V = ⊤ := by
    refine Opens.ext (Set.eq_univ_iff_forall.2 fun y => ?_)
    obtain ⟨z, rfl⟩ := p.surjective y
    rw [Opens.coe_iSup]
    exact Set.mem_iUnion.2 ⟨z, hVmem z⟩
  -- Over each `V z` the point descends, the chart being an affine formal spectrum.
  have hlocal : ∀ z : ↥T', ∃ s : schemeToFormalScheme.obj (V z).toScheme ⟶ X,
      schemeToFormalScheme.map (pullback.fst p (V z).ι) ≫ f
        = schemeToFormalScheme.map (pullback.snd p (V z).ι) ≫ s := fun z => by
    have := hlin (f.hom.toHom.base z)
    exact exists_comp_eq_pullback_snd_of_isoSpf X p f hcompat (V z) _ (A _).α (hadm _)
      (hiso _).some fun w hw => hw w rfl
  choose s hs using hlocal
  exact exists_comp_eq_of_opensCover_of_flat X p f V hVcover s hs

end AlgebraicGeometry

end
