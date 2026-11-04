module

public import Mathlib.CategoryTheory.Sites.Equivalence
public import StacksFrontier.AlgebraicGeometry.Topologies.ChangeOfSites.CoverPreserving
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Topologies.BigSites.ZariskiSiteAxioms

/-!
# The small Zariski site of a scheme and its topological space

For a scheme `S` in a big Zariski site, sending an object of the small Zariski site of `S` to
the open image of its structure morphism is an equivalence of categories onto the opens of the
underlying topological space of `S`, and it matches the small Zariski topology with the usual
topology on opens. Consequently sheaves on the small Zariski site are the same thing as
sheaves on the space of `S`, with values in any category.

## Main definitions

* `AlgebraicGeometry.smallZariskiToOpens`: the open-image functor.
* `AlgebraicGeometry.smallZariskiSiteEquiv`: the resulting equivalence of categories.
* `AlgebraicGeometry.smallZariskiSheafEquivWith`, `AlgebraicGeometry.smallZariskiSheafEquiv`:
  the induced equivalence of sheaf categories, for arbitrary coefficients and for sheaves of
  sets.

## Main results

* `AlgebraicGeometry.smallZariskiToOpens_isEquivalence_and_isDenseSubsite`: the open-image
  functor is an equivalence of categories and a dense subsite.
* `AlgebraicGeometry.smallZariskiSheafEquiv_functor`,
  `AlgebraicGeometry.smallZariskiSheafEquiv_inverse`,
  `AlgebraicGeometry.smallZariskiSheafEquiv_inverse_obj`: the underlying presheaves of the
  comparison and of its inverse, and the sections of the inverse.
* `AlgebraicGeometry.openImmersion_ΓIsoTop_inv`,
  `AlgebraicGeometry.openImmersion_ΓIsoTop_naturality`: the isomorphism between the global
  sections of the source of an open immersion and the sections over its open image is a
  restriction map, natural in the open immersion.

## References

* [Stacks Project, Tag 020X](https://stacks.math.columbia.edu/tag/020X)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory TopologicalSpace Opposite

universe u v w v₁ w₁

namespace AlgebraicGeometry


variable (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The open immersion into `S` underlying an object of the small Zariski site of `S`. -/
public abbrev smallZariskiOpenImmersion (X : SmallZariski B S hS) :
    (SmallZariski.toScheme B S hS).obj X ⟶ S :=
  B.inclusion.map X.obj.hom

/-- A small-site morphism commutes with the maps to the base scheme. -/
public lemma smallZariskiOpenImmersion_comp {X Y : SmallZariski B S hS}
    (f : X ⟶ Y) :
    (SmallZariski.toScheme B S hS).map f ≫
      smallZariskiOpenImmersion B S hS Y = smallZariskiOpenImmersion B S hS X :=
  (B.inclusion.map_comp f.hom.left Y.obj.hom).symm.trans
    (congrArg B.inclusion.map f.hom.w)

private noncomputable def smallZariskiOpenObject (U : S.Opens) :
    SmallZariski B S hS := by
  let U₀ : B.Schemes := ⟨(U : Scheme), (Scheme.size_coe_opens_le S U).trans_lt hS⟩
  let S₀ : B.Schemes := ⟨S, hS⟩
  let i : U₀ ⟶ S₀ := ObjectProperty.homMk U.ι
  refine ⟨Over.mk i, ?_⟩
  change IsOpenImmersion (B.inclusion.map i)
  simpa [i] using (inferInstance : IsOpenImmersion U.ι)

/-- The functor from the small Zariski site of `S` to the opens of `S` sending an object to the
open image of its open immersion into `S`. -/
public def smallZariskiToOpens : SmallZariski B S hS ⥤ Opens S.carrier where
  obj X := (smallZariskiOpenImmersion B S hS X).opensRange
  map {X Y} f := homOfLE (by
    change Set.range (smallZariskiOpenImmersion B S hS X) ⊆
      Set.range (smallZariskiOpenImmersion B S hS Y)
    rw [← smallZariskiOpenImmersion_comp B S hS f]
    rintro _ ⟨x, rfl⟩
    exact ⟨((SmallZariski.toScheme B S hS).map f) x,
      (Scheme.Hom.comp_apply _ _ x).symm⟩)

private instance smallZariskiToOpens_faithful :
    (smallZariskiToOpens B S hS).Faithful where
  map_injective := by
    intro X Y f g h
    refine ObjectProperty.hom_ext _ (Over.OverMorphism.ext (B.inclusion.map_injective ?_))
    rw [← cancel_mono (B.inclusion.map Y.obj.hom), ← Functor.map_comp, ← Functor.map_comp,
      f.hom.w, g.hom.w]

private instance smallZariskiToOpens_full :
    (smallZariskiToOpens B S hS).Full where
  map_surjective := by
    intro X Y q
    let hh := B.inclusion.map X.obj.hom
    let gg := B.inclusion.map Y.obj.hom
    have : IsOpenImmersion hh := X.property
    have : IsOpenImmersion gg := Y.property
    have hset : Set.range hh ⊆ Set.range gg := q.le
    refine ⟨ObjectProperty.homMk (Over.homMk
      (B.inclusion.preimage (IsOpenImmersion.lift gg hh hset)) (B.inclusion.map_injective ?_)),
      Subsingleton.elim _ _⟩
    rw [B.inclusion.map_comp, B.inclusion.map_preimage]
    exact IsOpenImmersion.lift_fac gg hh hset

private instance smallZariskiToOpens_essSurj :
    (smallZariskiToOpens B S hS).EssSurj where
  mem_essImage U := by
    refine ⟨smallZariskiOpenObject B S hS U, ⟨eqToIso ?_⟩⟩
    simp [smallZariskiToOpens, smallZariskiOpenObject]

private noncomputable def openCoverArrowData (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : SmallZariski B S hS) (R : Presieve X)
    (hR : R.map (smallZariskiToOpens B S hS) ∈ Opens.pretopology S.carrier
      ((smallZariskiToOpens B S hS).obj X)) (x : ↥(B.inclusion.obj X.obj.left)) :
    Σ Z : SmallZariski B S hS, Σ g : Z ⟶ X,
      PLift (R g) × Σ y : B.inclusion.obj Z.obj.left,
        PLift ((B.inclusion.map Z.obj.hom) y = (B.inclusion.map X.obj.hom) x) := by
  classical
  have hex : ∃ Z : SmallZariski B S hS, ∃ g : Z ⟶ X, R g ∧ ∃ y : B.inclusion.obj Z.obj.left,
      (B.inclusion.map Z.obj.hom) y = (B.inclusion.map X.obj.hom) x := by
    let u : (smallZariskiToOpens B S hS).obj X :=
      ⟨(B.inclusion.map X.obj.hom) x, Scheme.Hom.mem_opensRange.mpr ⟨x, rfl⟩⟩
    change ∀ x ∈ (smallZariskiToOpens B S hS).obj X,
      ∃ (V : S.Opens) (f : V ⟶ (smallZariskiToOpens B S hS).obj X),
        (R.map (smallZariskiToOpens B S hS)) f ∧ x ∈ V at hR
    obtain ⟨V, q, hq, hu⟩ := hR u.1 u.2
    obtain ⟨Z, rfl, g, hg, hmap⟩ := (Presieve.map_iff.mp hq)
    simp only [eqToHom_refl, Category.id_comp] at hmap
    have hZ : u.1 ∈ (B.inclusion.map Z.obj.hom).opensRange := by
      simpa [smallZariskiToOpens, smallZariskiOpenImmersion] using hu
    obtain ⟨y, hy⟩ := Scheme.Hom.mem_opensRange.mp hZ
    exact ⟨Z, g, hg, y, hy⟩
  let Z := Classical.choose hex
  have hg : ∃ g : Z ⟶ X, R g ∧ ∃ y : B.inclusion.obj Z.obj.left,
      (B.inclusion.map Z.obj.hom) y = (B.inclusion.map X.obj.hom) x :=
    Classical.choose_spec hex
  let g := Classical.choose hg
  have hr : R g ∧ ∃ y : B.inclusion.obj Z.obj.left,
      (B.inclusion.map Z.obj.hom) y = (B.inclusion.map X.obj.hom) x := Classical.choose_spec hg
  let hy' := hr.2
  let y := Classical.choose hy'
  have hy := Classical.choose_spec hy'
  exact ⟨Z, g, ⟨hr.1⟩, y, ⟨hy⟩⟩

private noncomputable def arbitraryOpenCoverData (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : SmallZariski B S hS) (R : Presieve X)
    (hR : R.map (smallZariskiToOpens B S hS) ∈ Opens.pretopology S.carrier
      ((smallZariskiToOpens B S hS).obj X)) :
    Σ _ : Scheme.OpenCover.{u} (B.inclusion.obj X.obj.left),
      ∀ x : ↥(B.inclusion.obj X.obj.left),
        PLift (R ((openCoverArrowData B S hS X R hR x).2.1)) := by
  classical
  let I : Type u := ↥(B.inclusion.obj X.obj.left)
  let src (x : I) := B.inclusion.obj (openCoverArrowData B S hS X R hR x).1.obj.left
  let arr (x : I) : src x ⟶ B.inclusion.obj X.obj.left :=
    B.inclusion.map ((openCoverArrowData B S hS X R hR x).2.1.hom.left)
  have hcomp (x : I) : arr x ≫ B.inclusion.map X.obj.hom =
      B.inclusion.map (openCoverArrowData B S hS X R hR x).1.obj.hom :=
    smallZariskiOpenImmersion_comp B S hS (openCoverArrowData B S hS X R hR x).2.1
  have hprop (x : I) : IsOpenImmersion (arr x) := by
    have : IsOpenImmersion (B.inclusion.map (openCoverArrowData B S hS X R hR x).1.obj.hom) :=
      (openCoverArrowData B S hS X R hR x).1.property
    have : IsOpenImmersion (B.inclusion.map X.obj.hom) := X.property
    have : IsOpenImmersion (arr x ≫ B.inclusion.map X.obj.hom) := by rw [hcomp]; infer_instance
    exact IsOpenImmersion.of_comp (arr x) (B.inclusion.map X.obj.hom)
  let U : Scheme.OpenCover.{u} (B.inclusion.obj X.obj.left) :=
    Scheme.Cover.mkOfCovers.{u, u} I src arr (by
      intro x
      refine ⟨x, (openCoverArrowData B S hS X R hR x).2.2.2.1, ?_⟩
      apply (Scheme.Hom.isOpenEmbedding (B.inclusion.map X.obj.hom)).injective
      calc
        (B.inclusion.map X.obj.hom) (arr x ((openCoverArrowData B S hS X R hR x).2.2.2.1)) =
            (B.inclusion.map (openCoverArrowData B S hS X R hR x).1.obj.hom)
                ((openCoverArrowData B S hS X R hR x).2.2.2.1) := by
              simpa only [Scheme.Hom.comp_apply] using congrArg
                (fun f => f ((openCoverArrowData B S hS X R hR x).2.2.2.1)) (hcomp x)
        _ = (B.inclusion.map X.obj.hom) x :=
          (openCoverArrowData B S hS X R hR x).2.2.2.2.down) hprop
  refine ⟨U, ?_⟩
  intro x
  exact ⟨(openCoverArrowData B S hS X R hR x).2.2.1.down⟩

private lemma sieve_generate_of_iso_factor {X Y W : SmallZariski B S hS} {R : Presieve X}
    {g : Y ⟶ X} {k : W ⟶ X} (hg : R g)
    (e : B.inclusion.obj W.obj.left ≅ B.inclusion.obj Y.obj.left)
    (he : e.hom ≫ B.inclusion.map g.hom.left = B.inclusion.map k.hom.left) :
    Sieve.generate R k := by
  let m : W.obj.left ⟶ Y.obj.left := B.inclusion.preimage e.hom
  have hmcomp : m ≫ g.hom.left = k.hom.left :=
    B.inclusion.map_injective (by rwa [Functor.map_comp, Functor.map_preimage])
  let mg : W ⟶ Y := ObjectProperty.homMk (Over.homMk m (by
    rw [← Over.w k.hom, ← hmcomp, Category.assoc, Over.w g.hom]))
  exact ⟨Y, mg, g, hg, ObjectProperty.hom_ext _ (Over.OverMorphism.ext hmcomp)⟩

private theorem boundedSiteCoverRefines (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) (X : SmallZariski B S hS) (R : Presieve X)
    (hR : R.map (smallZariskiToOpens B S hS) ∈ Opens.pretopology S.carrier
      ((smallZariskiToOpens B S hS).obj X)) :
    ∃ E : PreZeroHypercover.{u + 1} X,
      SmallZariski.IsCovering B S hS ⟨X, E⟩ ∧
        E.presieve₀ ≤ Sieve.generate R := by
  classical
  let d := arbitraryOpenCoverData B S hS X R hR
  let U := d.1
  obtain ⟨V, hV, hEq⟩ :=
    BigZariskiSite.exists_isCovering_tautologicallyEquivalent_openCover B X.obj.left U
  have hindex : U.I₀ = ↥(B.inclusion.obj X.obj.left) := rfl
  let beta : V.I₀ → U.I₀ := hEq.2.choose
  have hb (i : V.I₀) : ∃ e : B.inclusion.obj (V.X i) ≅
      B.inclusion.obj ((openCoverArrowData B S hS X R hR (hindex ▸ beta i)).1.obj.left),
        e.hom ≫ U.f (beta i) = B.inclusion.map (V.f i) := by
    obtain ⟨e, he⟩ := hEq.2.choose_spec i
    refine ⟨e, ?_⟩
    change e.hom ≫ U.f (hEq.2.choose i) = B.inclusion.map (V.f i)
    simpa [PreZeroHypercover.map] using he
  let Z (i : V.I₀) : SmallZariski B S hS := by
    have : IsOpenImmersion (B.inclusion.map X.obj.hom) := X.property
    have : IsOpenImmersion (B.inclusion.map (V.f i)) := by
      rw [← (hb i).choose_spec]
      exact @IsOpenImmersion.comp _ _ _ _ _ (IsOpenImmersion.of_isIso _) (U.map_prop (beta i))
    refine ⟨Over.mk (V.f i ≫ X.obj.hom), ?_⟩
    change IsOpenImmersion (B.inclusion.map (V.f i ≫ X.obj.hom))
    rw [B.inclusion.map_comp]
    infer_instance
  let E : PreZeroHypercover.{u + 1} X :=
    { I₀ := V.I₀
      X := Z
      f := fun i => ObjectProperty.homMk (Over.homMk (V.f i) (by rfl)) }
  refine ⟨E, hV, ?_⟩
  rw [Presieve.ofArrows_le_iff]
  intro i
  obtain ⟨e, he⟩ := hb i
  exact sieve_generate_of_iso_factor B S hS (d.2 (hindex ▸ beta i)).down e he

private lemma scheme_eqToHom_point {X Y : Scheme.{u}} (h : X = Y) (y : Y) :
    (eqToHom h) (h.symm ▸ y) = y := by
  cases h
  rfl

private lemma smallPrecoverage_map_mem_opensPretopology
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : SmallZariski B S hS) (E : PreZeroHypercover X)
    (hE : B.IsCovering ⟨X.obj.left,
      E.map (SmallZariski.inclusion B S hS ⋙ BigZariskiOver.inclusion B S hS)⟩) :
    E.presieve₀.map (smallZariskiToOpens B S hS) ∈ Opens.pretopology S.carrier
      ((smallZariskiToOpens B S hS).obj X) := by
  classical
  let F := SmallZariski.toScheme B S hS
  have hZ : (E.map F).presieve₀ ∈ Scheme.zariskiPretopology (B.inclusion.obj X.obj.left) := by
    change (E.map (SmallZariski.inclusion B S hS ⋙
      BigZariskiOver.inclusion B S hS ⋙ B.inclusion)).presieve₀ ∈ _
    simpa [IsZariskiCovering, SmallZariski.toScheme,
      BigZariskiOver.toScheme, BigZariskiOver.inclusion,
      SmallZariski.inclusion, PreZeroHypercover.map] using hE.1
  obtain ⟨W, hEq⟩ := Scheme.exists_cover_of_mem_pretopology hZ
  have hjointW := (Scheme.ofArrows_mem_precoverage_iff
    (P := @IsOpenImmersion) (S := B.inclusion.obj X.obj.left)
    (X := W.X) (f := W.f)).mp (by simpa [PreZeroHypercover.presieve₀] using W.mem₀)
  change ∀ x ∈ (smallZariskiToOpens B S hS).obj X,
    ∃ (V : S.Opens) (f : V ⟶ (smallZariskiToOpens B S hS).obj X),
      (E.presieve₀.map (smallZariskiToOpens B S hS)) f ∧ x ∈ V
  intro x hx
  obtain ⟨p, hp⟩ := Scheme.Hom.mem_opensRange.mp hx
  obtain ⟨i, y, hy⟩ := hjointW.1 p
  have hmem : (E.map F).presieve₀ (W.f i) := by
    rw [hEq]
    exact ⟨i⟩
  rw [PreZeroHypercover.presieve₀_map] at hmem
  obtain ⟨A, hsrc, g, hg, hmap⟩ := Presieve.map_iff.mp hmem
  let yA : F.obj A := hsrc.symm ▸ y
  have hcast : (eqToHom hsrc) yA = y := scheme_eqToHom_point hsrc y
  have hpoint : F.map g yA = (W.f i) y := by
    have h := congrArg (fun f => f yA) hmap
    change F.map g yA = (eqToHom hsrc ≫ W.f i) yA at h
    rwa [Scheme.Hom.comp_apply, hcast] at h
  have hpoint' : (B.inclusion.map g.hom.left) yA = p := by
    simpa [F, SmallZariski.toScheme, SmallZariski.inclusion,
      BigZariskiOver.toScheme, BigZariskiOver.inclusion] using hpoint.trans hy
  have hcomp : B.inclusion.map g.hom.left ≫ B.inclusion.map X.obj.hom =
      B.inclusion.map A.obj.hom := smallZariskiOpenImmersion_comp B S hS g
  refine ⟨(smallZariskiToOpens B S hS).obj A, (smallZariskiToOpens B S hS).map g, ?_, ?_⟩
  · exact Presieve.map_map hg
  · apply Scheme.Hom.mem_opensRange.mpr
    refine ⟨yA, ?_⟩
    calc
      (B.inclusion.map A.obj.hom) yA =
          (B.inclusion.map X.obj.hom) ((B.inclusion.map g.hom.left) yA) := by
            simpa only [Scheme.Hom.comp_apply] using
              (congrArg (fun f => f yA) hcomp).symm
      _ = (B.inclusion.map X.obj.hom) p := by rw [hpoint']
      _ = x := hp

private theorem smallPrecoverage_maps_to_opens
    (B : BigZariskiSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (X : SmallZariski B S hS) (R : Presieve X)
    (hR : R ∈ SmallZariski.precoverage B S hS X) :
    Sieve.generate (R.map (smallZariskiToOpens B S hS)) ∈
      Opens.grothendieckTopology S.carrier ((smallZariskiToOpens B S hS).obj X) := by
  obtain ⟨E, rfl, hE⟩ := SmallZariski.mem_precoverage_iff B S hS |>.mp hR
  have hopen := smallPrecoverage_map_mem_opensPretopology B S hS X E hE
  rw [Opens.mem_grothendieckTopology]
  intro x hx
  obtain ⟨V, f, hf, hxV⟩ := hopen x hx
  exact ⟨V, f, Sieve.le_generate _ V f hf, hxV⟩

private noncomputable def smallOpensEquiv (B : BigZariskiSite.{u}) (S : Scheme.{u})
    (hS : B.Contains S) : SmallZariski B S hS ≌ S.Opens := by
  letI : (smallZariskiToOpens B S hS).IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  exact (smallZariskiToOpens B S hS).asEquivalence

private theorem smallZariskiToOpens_coverPreserving (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    CoverPreserving (SmallZariski.topology B S hS)
      (Opens.grothendieckTopology S.carrier) (smallZariskiToOpens B S hS) := by
  have : (smallZariskiToOpens B S hS).IsEquivalence := ⟨inferInstance, inferInstance, inferInstance⟩
  refine coverPreserving_of_generators (smallZariskiToOpens B S hS)
    (SmallZariski.precoverage B S hS) (Opens.grothendieckTopology S.carrier) ?_
  intro X R hR
  rw [← Sieve.generate_map_eq_functorPushforward]
  exact smallPrecoverage_maps_to_opens B S hS X R hR

private theorem opensToSmall_coverPreserving (B : BigZariskiSite.{u})
    (S : Scheme.{u}) (hS : B.Contains S) :
    CoverPreserving (Opens.grothendieckTopology S.carrier)
      (SmallZariski.topology B S hS)
      (smallOpensEquiv B S hS).inverse := by
  classical
  let e := smallOpensEquiv B S hS
  let F := e.functor
  let G := e.inverse
  let J := SmallZariski.topology B S hS
  constructor
  intro U T hT
  let X : SmallZariski B S hS := G.obj U
  let R : Presieve X := (T.functorPushforward G).arrows
  have hR : R.map F ∈ Opens.pretopology S.carrier (F.obj X) := by
    change ∀ x ∈ F.obj X, ∃ (V : S.Opens) (f : V ⟶ F.obj X), R.map F f ∧ x ∈ V
    intro x hx
    obtain ⟨V, f, hf, hxV⟩ :=
      (Opens.mem_grothendieckTopology (T := S.carrier)).mp hT x ((e.counitIso.app U).hom.le hx)
    have hVeq : F.obj (G.obj V) = V :=
      le_antisymm (e.counitIso.app V).hom.le (e.counitIso.app V).inv.le
    refine ⟨F.obj (G.obj V), F.map (G.map f), ?_, hVeq.symm ▸ hxV⟩
    exact Presieve.map_map (show T.functorPushforward G (G.map f) from ⟨V, f, 𝟙 _, hf, by simp⟩)
  obtain ⟨E, hE, hle⟩ := boundedSiteCoverRefines B S hS X R hR
  have hgenR : Sieve.generate R ∈ J X :=
    J.superset_covering ((Sieve.generate_le_iff _ _).2 hle)
      (Precoverage.generate_mem_toGrothendieck ⟨E, rfl, hE⟩)
  change Sieve.generate (T.functorPushforward G).arrows ∈ J X at hgenR
  rwa [Sieve.generate_sieve] at hgenR

/-- The open-image functor `smallZariskiToOpens B S hS` is an equivalence of categories, and it
is a dense subsite for the small Zariski topology of `S` and the topology of the opens of `S`. -/
public theorem smallZariskiToOpens_isEquivalence_and_isDenseSubsite :
    (smallZariskiToOpens B S hS).IsEquivalence ∧
      (smallZariskiToOpens B S hS).IsDenseSubsite
        (SmallZariski.topology B S hS)
        (Opens.grothendieckTopology S.carrier) := by
  refine ⟨⟨inferInstance, inferInstance, inferInstance⟩, ?_⟩
  let e := smallOpensEquiv B S hS
  let J := SmallZariski.topology B S hS
  let K := Opens.grothendieckTopology S.carrier
  have : e.functor.IsCocontinuous J K :=
    (e.toAdjunction.isCocontinuous_iff_coverPreserving J K).2 (opensToSmall_coverPreserving B S hS)
  have : e.inverse.IsCocontinuous K J :=
    (e.symm.toAdjunction.isCocontinuous_iff_coverPreserving K J).2
      (smallZariskiToOpens_coverPreserving B S hS)
  have : e.inverse.IsDenseSubsite K J := Equivalence.isDenseSubsite_inverse_of_isCocontinuous J K e
  change e.functor.IsDenseSubsite J K
  exact Equivalence.isDenseSubsite_functor_of_isCocontinuous J K e

/-- The open-image functor `smallZariskiToOpens B S hS` is an equivalence of categories. -/
public noncomputable instance smallZariskiToOpens_isEquivalence :
    (smallZariskiToOpens B S hS).IsEquivalence :=
  (smallZariskiToOpens_isEquivalence_and_isDenseSubsite B S hS).1

/-- The open-image functor `smallZariskiToOpens B S hS` is a dense subsite for the small
Zariski topology of `S` and the topology of the opens of `S`. -/
public instance smallZariskiToOpens_isDenseSubsite :
    (smallZariskiToOpens B S hS).IsDenseSubsite
      (SmallZariski.topology B S hS)
      (Opens.grothendieckTopology S.carrier) :=
  (smallZariskiToOpens_isEquivalence_and_isDenseSubsite B S hS).2

/-- The equivalence of categories between the small Zariski site of `S` and the opens of `S`
whose functor is `smallZariskiToOpens B S hS`. -/
public noncomputable def smallZariskiSiteEquiv :
    SmallZariski B S hS ≌ Opens S.carrier :=
  (smallZariskiToOpens B S hS).asEquivalence

/-- The inverse of `smallZariskiSiteEquiv B S hS` is a dense subsite for the topology of the
opens of `S` and the small Zariski topology of `S`. -/
public instance smallZariskiSiteEquiv_inverse_isDenseSubsite :
    (smallZariskiSiteEquiv B S hS).inverse.IsDenseSubsite
      (Opens.grothendieckTopology S.carrier)
      (SmallZariski.topology B S hS) := by
  have : (smallZariskiSiteEquiv B S hS).symm.inverse.IsDenseSubsite
      (SmallZariski.topology B S hS)
      (Opens.grothendieckTopology S.carrier) :=
    smallZariskiToOpens_isDenseSubsite B S hS
  exact inferInstanceAs ((smallZariskiSiteEquiv B S hS).symm.functor.IsDenseSubsite _ _)

/-- The equivalence between sheaves with values in a category `A` on the small Zariski site of
`S` and on the opens of `S`, induced by `smallZariskiSiteEquiv B S hS`. -/
@[stacks 020X]
public noncomputable def smallZariskiSheafEquivWith (A : Type w) [Category.{v} A] :
    Sheaf (SmallZariski.topology B S hS) A ≌
      Sheaf (Opens.grothendieckTopology S.carrier) A :=
  (smallZariskiSiteEquiv B S hS).sheafCongr _ _ A

/-- The equivalence between sheaves of sets on the small Zariski site of `S` and on the opens
of `S`. -/
public noncomputable def smallZariskiSheafEquiv :
    Sheaf (SmallZariski.topology B S hS) (Type v) ≌
      Sheaf (Opens.grothendieckTopology S.carrier) (Type v) :=
  smallZariskiSheafEquivWith B S hS (Type v)

/-- The presheaf underlying the image of a sheaf `F` under `smallZariskiSheafEquivWith` is `F`
precomposed with the inverse of `smallZariskiSiteEquiv B S hS`. -/
public theorem smallZariskiSheafEquiv_functor (A : Type w) [Category.{v} A]
    (F : Sheaf (SmallZariski.topology B S hS) A) :
    ((smallZariskiSheafEquivWith B S hS A).functor.obj F).obj =
      (smallZariskiSiteEquiv B S hS).inverse.op ⋙ F.obj := rfl

/-- The presheaf underlying the image of a sheaf `F` on the opens of `S` under the inverse of
`smallZariskiSheafEquivWith` is `F` precomposed with `smallZariskiToOpens B S hS`. -/
public theorem smallZariskiSheafEquiv_inverse (A : Type w) [Category.{v} A]
    (F : Sheaf (Opens.grothendieckTopology S.carrier) A) :
    ((smallZariskiSheafEquivWith B S hS A).inverse.obj F).obj =
      (smallZariskiToOpens B S hS).op ⋙ F.obj := rfl

/-- The sections over an object `X` of the image of a sheaf `F` on the opens of `S` under the
inverse of `smallZariskiSheafEquivWith` are the sections of `F` over the open image of `X`. -/
public theorem smallZariskiSheafEquiv_inverse_obj (A : Type w) [Category.{v} A]
    (F : Sheaf (Opens.grothendieckTopology S.carrier) A)
    (X : SmallZariski B S hS) :
    ((smallZariskiSheafEquivWith B S hS A).inverse.obj F).obj.obj (op X) =
      F.obj.obj (op (smallZariskiOpenImmersion B S hS X).opensRange) := rfl

/-- The presheaf underlying the image of a sheaf `F` under `smallZariskiSheafEquivWith`,
precomposed with `smallZariskiToOpens B S hS`, is isomorphic to the presheaf underlying `F`. -/
public noncomputable def smallZariskiSheafEquiv_sections (A : Type w) [Category.{v} A]
    (F : Sheaf (SmallZariski.topology B S hS) A) :
    (smallZariskiToOpens B S hS).op ⋙
        ((smallZariskiSheafEquivWith B S hS A).functor.obj F).obj ≅ F.obj :=
  (sheafToPresheaf _ _).mapIso
    ((smallZariskiSheafEquivWith B S hS A).unitIso.symm.app F)

/-- The comparison `smallZariskiSheafEquivWith` commutes with composing sheaves with a functor
`H : A ⥤ D`. -/
public noncomputable def smallZariskiSheafEquiv_comp
    {A : Type w} [Category.{v} A] {D : Type w₁} [Category.{v₁} D] (H : A ⥤ D)
    [(SmallZariski.topology B S hS).HasSheafCompose H]
    [(Opens.grothendieckTopology S.carrier).HasSheafCompose H] :
    (smallZariskiSheafEquivWith B S hS A).functor ⋙
        sheafCompose (Opens.grothendieckTopology S.carrier) H ≅
      sheafCompose (SmallZariski.topology B S hS) H ⋙
        (smallZariskiSheafEquivWith B S hS D).functor :=
  NatIso.ofComponents
    (fun F => ObjectProperty.isoMk _ (Functor.associator _ F.obj H))
    (by
      intro F G f
      ext X
      change H.map (f.hom.app _) ≫ 𝟙 _ = 𝟙 _ ≫ H.map (f.hom.app _)
      simp)

/-- For an open immersion `f : X ⟶ T`, the inverse of `IsOpenImmersion.ΓIsoTop f` is the map
`f.appLE` from the sections of `T` over the open image of `f` to the global sections of `X`. -/
public lemma openImmersion_ΓIsoTop_inv {X T : Scheme.{u}} (f : X ⟶ T) [IsOpenImmersion f] :
    (IsOpenImmersion.ΓIsoTop f).inv =
      f.appLE f.opensRange ⊤ (by simp) := by
  simp only [IsOpenImmersion.ΓIsoTop, Iso.trans_inv, Functor.mapIso_inv,
    Iso.op_inv, eqToIso.inv, eqToHom_op, Iso.symm_inv,
    Scheme.Hom.appIso_hom', Scheme.Hom.map_appLE]

/-- For open immersions `jX = f ≫ jY` and `jY` into `T`, the inverses of
`IsOpenImmersion.ΓIsoTop` commute with the restriction of sections of `T` from the open image of
`jY` to that of `jX` and with `f.appTop`. -/
public lemma openImmersion_ΓIsoTop_naturality {X Y T : Scheme.{u}} (f : X ⟶ Y)
    (jX : X ⟶ T) (jY : Y ⟶ T) [IsOpenImmersion jX] [IsOpenImmersion jY]
    (h : f ≫ jY = jX) (hle : jX.opensRange ≤ jY.opensRange) :
    T.presheaf.map (homOfLE hle).op ≫ (IsOpenImmersion.ΓIsoTop jX).inv =
      (IsOpenImmersion.ΓIsoTop jY).inv ≫ f.appTop := by
  subst jX
  rw [openImmersion_ΓIsoTop_inv, openImmersion_ΓIsoTop_inv, Scheme.Hom.map_appLE]
  have hf : f.appTop = f.appLE ⊤ ⊤ (by simp) := by
    rw [Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    congr 1
  rw [hf]
  exact (Scheme.Hom.appLE_comp_appLE f jY jY.opensRange ⊤ ⊤ (by simp) (by simp)).symm

end AlgebraicGeometry
