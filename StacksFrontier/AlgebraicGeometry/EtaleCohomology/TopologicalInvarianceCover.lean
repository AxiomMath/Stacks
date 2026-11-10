module

public import Mathlib.AlgebraicGeometry.Cover.Directed
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceGlue

/-!
# Descending an étale scheme along a universal homeomorphism from an open covering

Let `f : X ⟶ Y` be a universal homeomorphism. The essential image of base change along `f` on
étale schemes is closed under glueing along an arbitrary open covering, not only along a single
open subscheme: a scheme étale over `X` which is covered by open subschemes each of which is the
base change of a scheme étale over `Y` is itself such a base change.

The covering is presented as a locally directed open cover, so the descent is a locally directed
colimit and carries no cocycle obligation. Base change along `f` is fully faithful, so the chosen
descents of the members of the cover are canonically connected by transition morphisms, and those
morphisms are the maps of a diagram whose colimit is the descent of the whole scheme.

Since every open subscheme of a base change is again a base change, the open subschemes which are
base changes are closed downwards; hence as soon as they cover, they form a basis of the topology
and the open cover they index is locally directed by inclusion. This turns the glueing statement
into the criterion that the descended open subschemes cover.

## Main definitions

* `Stacks.Etale.descendedOpens` is the set of open subschemes of a scheme over `X` which are, over
  `X`, base changes along `f` of schemes étale over `Y`.

## Main results

* `Stacks.Etale.exists_etale_pullback_iso_of_locallyDirectedFamily` — the glueing of a locally
  directed diagram of schemes étale over `Y` whose base changes are the members of an open cover
  of a scheme over `X` is a descent of that scheme.
* `Stacks.Etale.existsUnique_hom_of_le_of_pullback_iso` and
  `Stacks.Etale.isOpenImmersion_of_le_of_pullback_iso` — the inclusion of one descended open
  subscheme in another is the base change of a unique morphism over `Y`, and that morphism is an
  open immersion.
* `Stacks.Etale.descendedOpens_of_le` and `Stacks.Etale.descendedOpens_isBasis` — the descended
  open subschemes are closed downwards, hence form a basis of the topology as soon as they cover.
* `Stacks.Etale.exists_etale_pullback_iso_of_descendedOpens_cover` — **a scheme étale over `X`
  each of whose points lies in a descended open subscheme is itself a base change**, in the
  elementary form consumed by
  `Stacks.Etale.essSurj_etalePullback_of_forall_exists_pullback_iso`.

## Implementation notes

The glueing is stated and proved for a diagram of schemes together with a family of structure
morphisms to `Y` and the naturality equation, rather than for a functor into
`AlgebraicGeometry.Scheme.Etale` or a cocone over the constant functor. Every object occurring in
the diagram chase is then a projection of a variable, so no spelling has to be unfolded for a
rewrite to be type-correct.

The transition morphisms of the diagram are obtained from
`Stacks.Etale.existsUnique_hom_of_pullback_hom`, which says that a morphism of base changes over
`X` is the base change of a unique morphism over `Y`. Functoriality is then forced by that
uniqueness, so the diagram is constructed without any compatibility having to be checked by hand.

The comparison morphism out of the given scheme is
`AlgebraicGeometry.Scheme.Cover.glueMorphismsOfLocallyDirected` followed by
`CategoryTheory.Limits.pullback.lift`; that it is an isomorphism is checked by exhibiting it as an
open immersion which is bijective on points. Openness is local on the source over the given cover,
where the morphism is the base change of a component inclusion of the colimit, and bijectivity
uses that the first projection of a base change along a universal homeomorphism is a
homeomorphism.

The descended open subschemes are closed downwards by `Stacks.Etale.exists_opens_overlap_iso`,
which descends an open subscheme of a base change; for the basis property this is applied to the
intersection of a descended open subscheme with an arbitrary open subscheme.

## References

* [EGA IV, Theorem 18.1.2]
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 039R](https://stacks.math.columbia.edu/tag/039R)
-/

@[expose] public section

noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace Stacks.Etale

open AlgebraicGeometry

variable {X Y : Scheme.{u}}

/-- The first projection of a base change along a universal homeomorphism is a homeomorphism. -/
theorem isHomeomorph_pullbackFst (f : X ⟶ Y) [UniversalHomeomorphism f] {V : Scheme.{u}}
    (q : V ⟶ Y) : IsHomeomorph (pullback.fst q f).base :=
  UniversalHomeomorphism.universally_isHomeomorph _ _ _ (IsPullback.of_hasPullback q f)

section Family

variable (f : X ⟶ Y) {U : Scheme.{u}} (p : U ⟶ X) (𝒰 : U.OpenCover) [Category 𝒰.I₀]
  [𝒰.LocallyDirected] [Quiver.IsThin 𝒰.I₀] [Small.{u} 𝒰.I₀] (D : 𝒰.I₀ ⥤ Scheme.{u})
  [∀ {i j : 𝒰.I₀} (a : i ⟶ j), IsOpenImmersion (D.map a)] (q : ∀ i, D.obj i ⟶ Y)

/-- **Glueing a locally directed diagram of base changes.** Let `f : X ⟶ Y` be a universal
homeomorphism, let `U` be a scheme over `X` with a locally directed open cover, and let `D` be a
diagram of schemes étale over `Y`, indexed by the same category, whose maps are open immersions
over `Y`. If the base change of `D` along `f` is identified with the cover, compatibly with the
transition morphisms and with the projections to `U`, then the colimit of `D` is étale over `Y`
and its base change is `U`. -/
theorem exists_etale_pullback_iso_of_locallyDirectedFamily [UniversalHomeomorphism f]
    (hqnat : ∀ {i j : 𝒰.I₀} (a : i ⟶ j), D.map a ≫ q j = q i) (hq : ∀ i, Etale (q i))
    (ε : ∀ i, 𝒰.X i ≅ pullback (q i) f)
    (hε : ∀ i, (ε i).hom ≫ pullback.snd (q i) f = 𝒰.f i ≫ p)
    (hεnat : ∀ {i j : 𝒰.I₀} (a : i ⟶ j), 𝒰.trans a ≫ (ε j).hom ≫ pullback.fst (q j) f =
      (ε i).hom ≫ pullback.fst (q i) f ≫ D.map a) :
    ∃ (V : Scheme.{u}) (v : V ⟶ Y) (_ : Etale v) (e : pullback v f ≅ U),
      e.hom ≫ p = pullback.snd v f := by
  classical
  -- the projection of a member of the cover to the corresponding object of the diagram
  let π (i : 𝒰.I₀) : 𝒰.X i ⟶ D.obj i := (ε i).hom ≫ pullback.fst (q i) f
  have hπdef (i) : π i = (ε i).hom ≫ pullback.fst (q i) f := rfl
  have hπ (i) : IsHomeomorph (π i).base :=
    (isHomeomorph_pullbackFst f (q i)).comp (Scheme.Hom.homeomorph (ε i).hom).isHomeomorph
  have hπnat {i j : 𝒰.I₀} (a : i ⟶ j) : 𝒰.trans a ≫ π j = π i ≫ D.map a := by
    simpa only [π, Category.assoc] using hεnat a
  -- a point of a member of the cover maps to a point of the diagram exactly along the transition
  have hπiff {l i : 𝒰.I₀} (a : l ⟶ i) (u : 𝒰.X l) (x : 𝒰.X i) :
      D.map a (π l u) = π i x ↔ 𝒰.trans a u = x := by
    rw [← (hπ i).injective.eq_iff, ← Scheme.Hom.comp_apply, ← hπnat,
      Scheme.Hom.comp_apply]
  -- the diagram is locally directed, so it has a colimit covered by its components
  have : (D ⋙ Scheme.forget).IsLocallyDirected := ⟨by
    intro i j k ai aj xi xj hij
    change D.map ai xi = D.map aj xj at hij
    obtain ⟨ui, rfl⟩ := (hπ i).surjective xi
    obtain ⟨uj, rfl⟩ := (hπ j).surjective xj
    have hu : 𝒰.trans ai ui = 𝒰.trans aj uj := (hπ k).injective (by
      simpa only [← Scheme.Hom.comp_apply, hπnat] using hij)
    obtain ⟨l, bi, bj, ul, hi, hj⟩ := 𝒰.exists_of_trans_eq_trans ai aj ui uj hu
    exact ⟨l, bi, bj, π l ul, (hπiff bi ul ui).2 hi, (hπiff bj ul uj).2 hj⟩⟩
  have hιopen (i : 𝒰.I₀) : IsOpenImmersion (colimit.ι D i) :=
    (Scheme.IsLocallyDirected.openCover D).map_prop i
  let v : colimit D ⟶ Y := colimit.desc D
    { pt := Y
      ι.app i := q i
      ι.naturality i j a := by simpa using hqnat a }
  have hv (i) : colimit.ι D i ≫ v = q i := colimit.ι_desc _ _
  have hvetale : Etale v := by
    have : IsZariskiLocalAtSource (@Etale : MorphismProperty Scheme.{u}) :=
      HasRingHomProperty.instIsZariskiLocalAtSource
    exact IsZariskiLocalAtSource.of_openCover (Scheme.IsLocallyDirected.openCover D)
      fun i ↦ (hv i ▸ hq i : Etale (colimit.ι D i ≫ v))
  -- the comparison morphism to the colimit, and to its base change
  let g : U ⟶ colimit D := 𝒰.glueMorphismsOfLocallyDirected
    (fun i ↦ π i ≫ colimit.ι D i)
    (fun a ↦ by rw [← Category.assoc, hπnat, Category.assoc, colimit.w])
  have hg (i) : 𝒰.f i ≫ g = π i ≫ colimit.ι D i :=
    𝒰.map_glueMorphismsOfLocallyDirected _ _ i
  have hgbij : Function.Bijective g.base := by
    refine ⟨fun x y hxy ↦ ?_, fun y ↦ ?_⟩
    · obtain ⟨i, xi, rfl⟩ := 𝒰.exists_eq x
      obtain ⟨j, xj, rfl⟩ := 𝒰.exists_eq y
      have h : colimit.ι D i (π i xi) = colimit.ι D j (π j xj) := by
        simpa only [← Scheme.Hom.comp_apply, hg] using hxy
      obtain ⟨k, ai, aj, z, hi, hj⟩ := (Scheme.IsLocallyDirected.ι_eq_ι_iff D).mp h
      obtain ⟨z, rfl⟩ := (hπ k).surjective z
      rw [← (hπiff ai z xi).1 hi, ← (hπiff aj z xj).1 hj, ← Scheme.Hom.comp_apply,
        ← Scheme.Hom.comp_apply]
      simp only [Scheme.Cover.trans_map]
    · obtain ⟨i, yi, rfl⟩ := Scheme.IsLocallyDirected.ι_jointly_surjective D y
      obtain ⟨xi, rfl⟩ := (hπ i).surjective yi
      exact ⟨𝒰.f i xi, by rw [← Scheme.Hom.comp_apply, hg, Scheme.Hom.comp_apply]⟩
  have w : g ≫ v = p ≫ f := 𝒰.hom_ext _ _ fun i ↦ by
    rw [← Category.assoc, hg, Category.assoc, hv, hπdef, Category.assoc, pullback.condition,
      reassoc_of% (hε i)]
  let κ : U ⟶ pullback v f := pullback.lift g p w
  have hκfst : κ ≫ pullback.fst v f = g := pullback.lift_fst _ _ _
  have hκsnd : κ ≫ pullback.snd v f = p := pullback.lift_snd _ _ _
  have hκ (i) : 𝒰.f i ≫ κ =
      (ε i).hom ≫ baseChangeOver f v (q i) (colimit.ι D i) (hv i) := by
    refine pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Category.assoc, hκfst, baseChangeOver_fst, hg, hπdef, Category.assoc]
    · rw [Category.assoc, Category.assoc, hκsnd, baseChangeOver_snd, hε i]
  have hκbij : Function.Bijective κ.base := by
    refine ⟨fun a b hab ↦ hgbij.1 ?_, fun b ↦ ?_⟩
    · simpa only [← hκfst, Scheme.Hom.comp_apply] using congrArg (pullback.fst v f).base hab
    · obtain ⟨a, ha⟩ := hgbij.2 ((pullback.fst v f).base b)
      exact ⟨a, (isHomeomorph_pullbackFst f v).injective
        (by simpa only [← Scheme.Hom.comp_apply, hκfst] using ha)⟩
  have : IsOpenImmersion κ := IsOpenImmersion.of_openCover_source κ 𝒰 hκbij.1 fun i ↦ by
    rw [hκ]
    have := hιopen i
    infer_instance
  have : IsIso κ := (isIso_iff_isOpenImmersion_and_surjective κ).2 ⟨inferInstance, ⟨hκbij.2⟩⟩
  exact ⟨colimit D, v, hvetale, (asIso κ).symm, by
    rw [Iso.symm_hom, Iso.inv_comp_eq, asIso_hom, hκsnd]⟩

end Family

section Descended

variable (f : X ⟶ Y) {U V W : Scheme.{u}} (p : U ⟶ X) {A B : U.Opens}

/-- **The inclusion of one descended open subscheme in another descends.** Let `A ≤ B` be open
subschemes of a scheme `U` over `X`, each realized as a base change along `f` of a scheme étale
over `Y`. The inclusion of `A` in `B` is the base change of a unique morphism over `Y` between the
two realizations. -/
theorem existsUnique_hom_of_le_of_pullback_iso [UniversalHomeomorphism f] (hAB : A ≤ B)
    {qA : V ⟶ Y} {qB : W ⟶ Y} [Etale qA] [Etale qB] (eA : pullback qA f ≅ A.toScheme)
    (hA : eA.hom ≫ A.ι ≫ p = pullback.snd qA f) (eB : pullback qB f ≅ B.toScheme)
    (hB : eB.hom ≫ B.ι ≫ p = pullback.snd qB f) :
    ∃! m : V ⟶ W, m ≫ qB = qA ∧ pullback.fst qA f ≫ m =
      (eA.hom ≫ U.homOfLE hAB ≫ eB.inv) ≫ pullback.fst qB f := by
  refine existsUnique_hom_of_pullback_hom f qA qB _ ?_
  rw [Category.assoc, Category.assoc, (Iso.inv_comp_eq eB).2 hB.symm,
    ← Category.assoc (U.homOfLE hAB), Scheme.homOfLE_ι, hA]

/-- The descended inclusion of one descended open subscheme in another is an open immersion: it is
the inclusion of the open subscheme which cuts out the smaller one inside the realization of the
larger one. -/
theorem isOpenImmersion_of_le_of_pullback_iso [UniversalHomeomorphism f] (hAB : A ≤ B)
    {qA : V ⟶ Y} {qB : W ⟶ Y} [Etale qA] [Etale qB] (eA : pullback qA f ≅ A.toScheme)
    (hA : eA.hom ≫ A.ι ≫ p = pullback.snd qA f) (eB : pullback qB f ≅ B.toScheme)
    (hB : eB.hom ≫ B.ι ≫ p = pullback.snd qB f) (m : V ⟶ W) (hmq : m ≫ qB = qA)
    (hmfst : pullback.fst qA f ≫ m =
      (eA.hom ≫ U.homOfLE hAB ≫ eB.inv) ≫ pullback.fst qB f) :
    IsOpenImmersion m := by
  obtain ⟨Z, t, ht⟩ := exists_opens_overlap_iso f qB hAB eB
  have hbco : t.inv ≫ baseChangeOver f qB (Z.ι ≫ qB) Z.ι rfl = U.homOfLE hAB ≫ eB.inv := by
    rw [← cancel_mono (eB.hom ≫ B.ι)]
    simp only [Category.assoc]
    rw [← ht, Iso.inv_hom_id_assoc, Iso.inv_hom_id_assoc, Scheme.homOfLE_ι]
  have htinv : t.inv ≫ pullback.snd (Z.ι ≫ qB) f = A.ι ≫ p := by
    rw [← baseChangeOver_snd f qB (Z.ι ≫ qB) Z.ι rfl, ← Category.assoc, hbco, Category.assoc,
      (Iso.inv_comp_eq eB).2 hB.symm, ← Category.assoc, Scheme.homOfLE_ι]
  have hd : (eA ≪≫ t.symm).hom ≫ pullback.snd (Z.ι ≫ qB) f = pullback.snd qA f := by
    rw [Iso.trans_hom, Iso.symm_hom, Category.assoc, htinv, hA]
  obtain ⟨δ, hδq, hδfst⟩ := exists_iso_of_pullback_iso f qA (Z.ι ≫ qB) (eA ≪≫ t.symm) hd
  obtain ⟨m', -, huniq⟩ := existsUnique_hom_of_le_of_pullback_iso f p hAB eA hA eB hB
  have hc1 : (δ.hom ≫ Z.ι) ≫ qB = qA := by simpa only [Category.assoc] using hδq
  have hc2 : pullback.fst qA f ≫ (δ.hom ≫ Z.ι) =
      (eA.hom ≫ U.homOfLE hAB ≫ eB.inv) ≫ pullback.fst qB f := by
    rw [← Category.assoc, hδfst, Iso.trans_hom, Iso.symm_hom]
    simp only [Category.assoc]
    rw [← baseChangeOver_fst f qB (Z.ι ≫ qB) Z.ι rfl, ← Category.assoc t.inv, hbco]
    simp only [Category.assoc]
  have hm : m = δ.hom ≫ Z.ι := (huniq m ⟨hmq, hmfst⟩).trans (huniq _ ⟨hc1, hc2⟩).symm
  rw [hm]
  infer_instance

/-- The open subschemes of a scheme `U` over `X` which are, over `X`, base changes along `f` of
schemes étale over `Y`. -/
def descendedOpens : Set U.Opens :=
  {A | ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ A.toScheme),
    e.hom ≫ A.ι ≫ p = pullback.snd q f}

/-- **The descended open subschemes are closed downwards.** An open subscheme of a descended open
subscheme is descended, because an open subscheme of a base change is a base change. -/
theorem descendedOpens_of_le [UniversalHomeomorphism f] (hB : B ∈ descendedOpens f p)
    (hAB : A ≤ B) : A ∈ descendedOpens f p := by
  obtain ⟨V, q, hq, e, he⟩ := hB
  have : Etale q := hq
  obtain ⟨Z, t, ht⟩ := exists_opens_overlap_iso f q hAB e
  refine ⟨Z.toScheme, Z.ι ≫ q, inferInstance, t, ?_⟩
  rw [← Category.assoc, ht, Category.assoc, Category.assoc, he,
    baseChangeOver_snd f q (Z.ι ≫ q) Z.ι rfl]

/-- **The descended open subschemes form a basis** as soon as they cover: they are closed
downwards, so the intersection of a descended open subscheme with an arbitrary one is descended. -/
theorem descendedOpens_isBasis [UniversalHomeomorphism f]
    (hcov : ∀ x : U, ∃ A ∈ descendedOpens f p, x ∈ A) :
    TopologicalSpace.Opens.IsBasis (descendedOpens f p) := by
  refine TopologicalSpace.Opens.isBasis_iff_nbhd.mpr fun {O x} hx ↦ ?_
  obtain ⟨A, hA, hxA⟩ := hcov x
  exact ⟨A ⊓ O, descendedOpens_of_le f p hA inf_le_left, ⟨hxA, hx⟩, inf_le_right⟩

/-- **A scheme over `X` covered by descended open subschemes is itself a base change.** Let
`f : X ⟶ Y` be a universal homeomorphism and let `p : U ⟶ X` be a morphism such that every point
of `U` lies in an open subscheme which is, over `X`, the base change along `f` of a scheme étale
over `Y`. Then `U` itself is the base change along `f` of a scheme étale over `Y`.

This is the essential surjectivity half of the topological invariance of the étale site, reduced
to its local form: it remains only to produce the local descents. -/
theorem exists_etale_pullback_iso_of_descendedOpens_cover [UniversalHomeomorphism f]
    (hcov : ∀ x : U, ∃ A ∈ descendedOpens f p, x ∈ A) :
    ∃ (V : Scheme.{u}) (q : V ⟶ Y) (_ : Etale q) (e : pullback q f ≅ U),
      e.hom ≫ p = pullback.snd q f := by
  classical
  choose Wo q hq eo heo using fun A : descendedOpens f p ↦ A.2
  let 𝒰 : U.OpenCover :=
    { I₀ := descendedOpens f p
      X := fun A ↦ (A.1 : U.Opens).toScheme
      f := fun A ↦ (A.1 : U.Opens).ι
      mem₀ := by
        rw [Scheme.presieve₀_mem_precoverage_iff]
        refine ⟨fun x ↦ ?_, fun _ ↦ inferInstance⟩
        obtain ⟨A, hA, hxA⟩ := hcov x
        exact ⟨⟨A, hA⟩, ⟨x, hxA⟩, rfl⟩ }
  let : PartialOrder 𝒰.I₀ := inferInstanceAs (PartialOrder (descendedOpens f p))
  have hrange : ∀ A : 𝒰.I₀, (𝒰.f A).opensRange = (A.1 : U.Opens) := fun A ↦
    Scheme.Opens.opensRange_ι _
  have hle {A B : 𝒰.I₀} : A ≤ B ↔ (𝒰.f A).opensRange ≤ (𝒰.f B).opensRange := by
    rw [hrange, hrange]
    exact Subtype.coe_le_coe.symm
  let : 𝒰.LocallyDirected := Scheme.Cover.LocallyDirected.ofIsBasisOpensRange hle (by
    have hset : (Set.range fun A : 𝒰.I₀ ↦ (𝒰.f A).opensRange) = descendedOpens f p := by
      refine Set.eq_of_subset_of_subset ?_ fun A hA ↦ ⟨⟨A, hA⟩, hrange ⟨A, hA⟩⟩
      rintro - ⟨A, rfl⟩
      change (𝒰.f A).opensRange ∈ descendedOpens f p
      rw [hrange]
      exact A.2
    rw [hset]
    exact descendedOpens_isBasis f p hcov)
  have htrans {A B : 𝒰.I₀} (a : A ⟶ B) : 𝒰.trans a = U.homOfLE (leOfHom a) :=
    (cancel_mono (𝒰.f B)).1 ((𝒰.trans_map a).trans (Scheme.homOfLE_ι _ _).symm)
  -- the transition morphisms of the diagram of chosen descents
  choose mo hmo hmuniq using fun (A B : 𝒰.I₀) (a : A ⟶ B) ↦
    existsUnique_hom_of_le_of_pullback_iso f p (leOfHom a) (eo A) (heo A) (eo B) (heo B)
  let D : 𝒰.I₀ ⥤ Scheme.{u} :=
    { obj := Wo
      map := fun {A B} a ↦ mo A B a
      map_id := fun A ↦ (hmuniq A A (𝟙 A) (𝟙 (Wo A)) ⟨Category.id_comp _, by
        rw [Category.comp_id, show U.homOfLE (leOfHom (𝟙 A)) = 𝟙 (A.1 : U.Opens).toScheme from
          U.homOfLE_rfl _, Category.id_comp, Iso.hom_inv_id, Category.id_comp]⟩).symm
      map_comp := fun {A B C} a b ↦ by
        refine (hmuniq A C (a ≫ b) (mo A B a ≫ mo B C b) ⟨?_, ?_⟩).symm
        · rw [Category.assoc, (hmo B C b).1, (hmo A B a).1]
        · rw [← Category.assoc, (hmo A B a).2]
          simp only [Category.assoc]
          rw [(hmo B C b).2]
          simp only [Category.assoc]
          rw [← Category.assoc (eo B).inv, Iso.inv_hom_id, Category.id_comp,
            ← Category.assoc (U.homOfLE (leOfHom a)), U.homOfLE_homOfLE] }
  have : ∀ {A B : 𝒰.I₀} (a : A ⟶ B), IsOpenImmersion (D.map a) := fun {A B} a ↦
    isOpenImmersion_of_le_of_pullback_iso f p (leOfHom a) (eo A) (heo A) (eo B) (heo B)
      (mo A B a) (hmo A B a).1 (hmo A B a).2
  refine exists_etale_pullback_iso_of_locallyDirectedFamily f p 𝒰 D q
    (fun {A B} a ↦ (hmo A B a).1) hq (fun A ↦ (eo A).symm) (fun A ↦ ?_) (fun {A B} a ↦ ?_)
  · rw [Iso.symm_hom, ← heo A, Iso.inv_hom_id_assoc]
  · rw [Iso.symm_hom, Iso.symm_hom, htrans a, show D.map a = mo A B a from rfl, (hmo A B a).2]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]

end Descended

end Stacks.Etale

end

end
