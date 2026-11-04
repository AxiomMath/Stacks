module

public import StacksFrontier.Algebra.Category.CommAlgCat.CoconeOfRingCocone
public import StacksFrontier.Algebra.Category.CommAlgCat.FilteredColimits
public import StacksFrontier.RingTheory.Flat.FlatteningFGApprox

/-!
# The local flattening functor is limit preserving

In the situation of Stacks Tag 05MK — a local homomorphism `A → B` of local rings and a
`B`-module `M`, tested against the category `C` of local `A`-algebras with local structure map —
the functor `F_lf` of Stacks Tag 05MM is limit preserving as soon as `A → B` is essentially of
finite presentation and `M` is a `B`-module of finite presentation. This is part (2) of
Stacks Tag 05MN.

A directed system in `C` is a filtered diagram `F : Λ ⥤ LocalAlgCat A`, and its colimit is read
off the colimit of the underlying diagram of `A`-algebras: a cocone `τ` of `F` is a colimit in
the relevant sense when its image under the forgetful functor `LocalAlgCat.toCommAlgCat` is a
colimit of `A`-algebras. Such an apex is again a local ring and the maps into it are again
local, which is `LocalAlgCat.isLocalRing_pt_of_isColimit` and
`LocalAlgCat.isLocalHom_ι_of_isColimit`, so the colimit does lie in `C`; this is assembled into
`LocalAlgCat.colimitCocone`, whose image under the forgetful functor is the colimit cocone of
`A`-algebras it was built from.

The content of part (2) is the descent statement
`Module.FlatAtPointSituation.exists_condition_of_isColimit`: if the flatness condition of
Stacks Tag 05ML holds over the colimit, it already holds at some stage. It is Stacks Tag 05LT
(`Module.exists_isFlatAtPrimesOver_of_isColimit`) applied to the family of maximal ideals of the
stages, whose supremum in the apex is the maximal ideal of the apex
(`LocalAlgCat.iSup_map_maximalIdeal_eq`), because a local homomorphism reflects units.

## Main results

* `LocalAlgCat.toCommAlgCat`: the forgetful functor from the category `C` of Stacks Tag 05MK to
  `A`-algebras.
* `LocalAlgCat.isLocalRing_pt_of_isColimit` and `LocalAlgCat.isLocalHom_ι_of_isColimit`: a
  filtered colimit of local `A`-algebras along local homomorphisms is again one, so `C` is
  closed under the directed colimits of part (2).
* `LocalAlgCat.colimitPt`, `LocalAlgCat.colimitCocone` and
  `LocalAlgCat.isColimitMapCoconeColimitCocone`: that closure, packaged as an object and a
  cocone of `C`; this is what makes the hypotheses of part (2) satisfiable.
* `LocalAlgCat.iSup_map_maximalIdeal_eq`: the maximal ideal of a local ring covered by local
  homomorphisms is the supremum of the extensions of the maximal ideals of the sources.
* `Module.FlatAtPointSituation.exists_condition_of_isColimit` and
  `Module.FlatAtPointSituation.condition_colimit_iff`: the flatness condition of Stacks Tag 05ML
  holds over a filtered colimit of local `A`-algebras exactly when it holds at some stage.
* `Module.FlatAtPointSituation.isColimitMapCoconeFlatAtPointFunctor`: **Stacks Tag 05MN
  part (2)**, `F_lf(colim A_i) = colim F_lf(A_i)`.

## Implementation notes

The only hypothesis on the colimit is that the cocone of `A`-algebras is a colimit. That it is
then a colimit elementwise — which is what expresses the source's directed colimit, and what
Stacks Tag 05LT asks for — is not assumed here but proved, by
`Stacks.CommAlgCat.forget_preservesFilteredColimitsOfSize`: a filtered colimit of commutative
algebras is computed on the underlying sets. That result carries a size condition on the index
category, namely that it be no larger than the algebras, because the forgetful functor of
commutative rings preserves filtered colimits at the size of the rings
(`CommRingCat.FilteredColimits.forget_preservesFilteredColimits`). The condition is recorded as
the two `UnivLE` hypotheses and is satisfied by a directed system in the sense of the source,
which is indexed by a set.

`F_lf` takes values in `PLift` of a proposition, so each of its values has at most one element.
Both hypotheses of `CategoryTheory.Limits.Types.FilteredColimit.isColimitOf` are therefore
cheap: the injectivity hypothesis is pure filteredness, and surjectivity is the descent
statement.

## References

* [Stacks Project, Tag 05MN](https://stacks.math.columbia.edu/tag/05MN)
* [Stacks Project, Tag 05LT](https://stacks.math.columbia.edu/tag/05LT)
* [Stacks Project, Tag 05MK](https://stacks.math.columbia.edu/tag/05MK)
* [Stacks Project, Tag 05ML](https://stacks.math.columbia.edu/tag/05ML)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits IsLocalRing

universe u v w x y z

namespace LocalAlgCat

variable {A : Type u} [CommRing A] [IsLocalRing A]

/-- The forgetful functor from the category `C` of local `A`-algebras of Stacks Tag 05MK to the
category of all `A`-algebras. The directed colimits of Stacks Tag 05MN part (2) are computed
here. -/
def toCommAlgCat : LocalAlgCat.{u, v} A ⥤ CommAlgCat.{v} A where
  obj R := CommAlgCat.of A R
  map f := CommAlgCat.ofHom f.hom
  map_id _ := rfl
  map_comp _ _ := rfl

/-- The underlying type of the image of a local `A`-algebra under `toCommAlgCat` is the algebra
itself. -/
@[simp]
theorem toCommAlgCat_obj (R : LocalAlgCat.{u, v} A) : (toCommAlgCat.obj R : Type v) = R := rfl

/-- The underlying algebra homomorphism of the image of a morphism under `toCommAlgCat` is the
underlying homomorphism of the morphism. -/
@[simp]
theorem toCommAlgCat_map_hom {R T : LocalAlgCat.{u, v} A} (f : R ⟶ T) :
    (toCommAlgCat.map f).hom = f.hom := rfl

/-- The maximal ideal of a local ring covered by a family of local homomorphisms is the supremum
of the extensions of the maximal ideals of the sources: a non-unit of the target has a non-unit
preimage, because a local homomorphism reflects units. -/
theorem iSup_map_maximalIdeal_eq {ι : Type*} {R : ι → Type v} {T : Type v}
    [∀ i, CommRing (R i)] [∀ i, IsLocalRing (R i)] [CommRing T] [IsLocalRing T]
    (g : ∀ i, R i →+* T) (hgl : ∀ i, IsLocalHom (g i))
    (hg : ∀ t : T, ∃ i, ∃ r : R i, g i r = t) :
    (⨆ i, Ideal.map (g i) (maximalIdeal (R i))) = maximalIdeal T := by
  refine le_antisymm (iSup_le fun i ↦ ?_) fun t ht ↦ ?_
  · have := hgl i
    exact IsLocalRing.map_maximalIdeal_le (g i)
  obtain ⟨i, r, rfl⟩ := hg t
  have hr : r ∈ maximalIdeal (R i) := by
    rw [mem_maximalIdeal]
    exact fun hu ↦ (mem_maximalIdeal _).mp ht (hu.map (g i))
  exact Ideal.mem_iSup_of_mem i (Ideal.mem_map_of_mem _ hr)

section Colimit

variable {Λ : Type y} [Category.{z} Λ] [IsFiltered Λ] (G : Λ ⥤ CommAlgCat.{v} A) (c : Cocone G)
  [UnivLE.{y, v}] [UnivLE.{z, v}]

omit [IsLocalRing A] in
/-- Two elements of a stage with the same image in the apex of a filtered colimit of
`A`-algebras become equal at a later stage. -/
theorem exists_map_eq_of_isColimit (hc : IsColimit c) {lam : Λ}
    {r r' : (G.obj lam : Type v)} (h : (c.ι.app lam).hom r = (c.ι.app lam).hom r') :
    ∃ (mu : Λ) (f : lam ⟶ mu), (G.map f).hom r = (G.map f).hom r' :=
  (Types.FilteredColimit.isColimit_eq_iff'
    (isColimitOfPreserves (forget (CommAlgCat.{v} A)) hc) r r').mp h

omit [IsLocalRing A] in
/-- The apex of a filtered colimit of nonzero `A`-algebras is nonzero: `1 = 0` in it would
already hold at a stage. -/
theorem nontrivial_pt_of_isColimit (hc : IsColimit c)
    (hnt : ∀ lam, Nontrivial (G.obj lam : Type v)) :
    Nontrivial (c.pt : Type v) := by
  obtain ⟨lam⟩ := IsFiltered.nonempty (C := Λ)
  refine ⟨⟨1, 0, fun h ↦ ?_⟩⟩
  have h' : (c.ι.app lam).hom (1 : (G.obj lam : Type v)) =
      (c.ι.app lam).hom (0 : (G.obj lam : Type v)) := by
    rw [map_one, map_zero]
    exact h
  obtain ⟨mu, f, hf⟩ := exists_map_eq_of_isColimit G c hc h'
  rw [map_one, map_zero] at hf
  have := hnt mu
  exact one_ne_zero hf

omit [IsLocalRing A] in
/-- **The category `C` of Stacks Tag 05MK is closed under filtered colimits**, first half: the
apex of a filtered colimit of local `A`-algebras is again a local ring. Every element of the
apex comes from a stage (`CommAlgCat.exists_app_eq`), where either it or `1` minus it is a
unit. -/
theorem isLocalRing_pt_of_isColimit (hc : IsColimit c)
    (hloc : ∀ lam, IsLocalRing (G.obj lam : Type v)) :
    IsLocalRing (c.pt : Type v) := by
  have := nontrivial_pt_of_isColimit G c hc fun lam ↦ by
    have := hloc lam
    infer_instance
  refine .of_isUnit_or_isUnit_one_sub_self fun t ↦ ?_
  obtain ⟨lam, r, rfl⟩ := CommAlgCat.exists_app_eq hc t
  have := hloc lam
  rcases IsLocalRing.isUnit_or_isUnit_one_sub_self r with hr | hr
  · exact Or.inl (hr.map (c.ι.app lam).hom)
  · have h := hr.map (c.ι.app lam).hom
    rw [map_sub, map_one] at h
    exact Or.inr h

omit [IsLocalRing A] in
/-- **The category `C` of Stacks Tag 05MK is closed under filtered colimits**, second half: the
structure maps into the apex of a filtered colimit of local `A`-algebras along local
homomorphisms are local homomorphisms. An element of a stage whose image in the apex is a unit
is inverted at a later stage, hence is already a unit there. -/
theorem isLocalHom_ι_of_isColimit (hc : IsColimit c)
    (hG : ∀ {lam mu : Λ} (f : lam ⟶ mu), IsLocalHom (G.map f).hom.toRingHom) (lam : Λ) :
    IsLocalHom (c.ι.app lam).hom.toRingHom := by
  refine ⟨fun r hr ↦ ?_⟩
  obtain ⟨s, hs⟩ := hr.exists_right_inv
  obtain ⟨mu, t, ht⟩ := CommAlgCat.exists_app_eq hc s
  have e : ∀ {kappa nu : Λ} (g : kappa ⟶ nu) (z : (G.obj kappa : Type v)),
      (c.ι.app nu).hom ((G.map g).hom z) = (c.ι.app kappa).hom z := fun {kappa nu} g z ↦
    congrArg (fun k : G.obj kappa ⟶ c.pt ↦ k.hom z) (c.w g)
  have key : (c.ι.app (IsFiltered.max lam mu)).hom
        ((G.map (IsFiltered.leftToMax lam mu)).hom r *
          (G.map (IsFiltered.rightToMax lam mu)).hom t) =
      (c.ι.app (IsFiltered.max lam mu)).hom (1 : (G.obj (IsFiltered.max lam mu) : Type v)) := by
    rw [map_mul, map_one, e (IsFiltered.leftToMax lam mu) r, e (IsFiltered.rightToMax lam mu) t,
      ht]
    exact hs
  obtain ⟨pi, f, hf⟩ := exists_map_eq_of_isColimit G c hc key
  rw [map_mul, map_one] at hf
  have hcomp : ∀ {kappa nu rho : Λ} (g : kappa ⟶ nu) (h : nu ⟶ rho) (z : (G.obj kappa : Type v)),
      (G.map (g ≫ h)).hom z = (G.map h).hom ((G.map g).hom z) := fun {kappa nu rho} g h z ↦
    congrArg (fun k : G.obj kappa ⟶ G.obj rho ↦ k.hom z) (G.map_comp g h)
  have hunit : IsUnit ((G.map (IsFiltered.leftToMax lam mu ≫ f)).hom r) := by
    refine IsUnit.of_mul_eq_one ((G.map (IsFiltered.rightToMax lam mu ≫ f)).hom t) ?_
    rw [hcomp (IsFiltered.leftToMax lam mu) f r, hcomp (IsFiltered.rightToMax lam mu) f t]
    exact hf
  have := hG (IsFiltered.leftToMax lam mu ≫ f)
  exact (isUnit_map_iff (G.map (IsFiltered.leftToMax lam mu ≫ f)).hom.toRingHom r).mp hunit

end Colimit

section LocalColimit

variable {Λ : Type y} [Category.{z} Λ] [IsFiltered Λ] (F : Λ ⥤ LocalAlgCat.{u, v} A)
  (c : Cocone (F ⋙ toCommAlgCat)) [UnivLE.{y, v}] [UnivLE.{z, v}]

/-- The apex of a colimit cocone of a filtered diagram of local `A`-algebras is a local ring. -/
theorem isLocalRing_pt (hc : IsColimit c) : IsLocalRing (c.pt : Type v) :=
  isLocalRing_pt_of_isColimit _ c hc fun lam ↦ inferInstanceAs (IsLocalRing (F.obj lam : Type v))

/-- The legs of a colimit cocone of a filtered diagram of local `A`-algebras are local
homomorphisms. -/
theorem isLocalHom_ι (hc : IsColimit c) (lam : Λ) : IsLocalHom (c.ι.app lam).hom.toRingHom :=
  isLocalHom_ι_of_isColimit _ c hc (fun f ↦ (F.map f).isLocal) lam

/-- The structure map of the apex of a colimit cocone of a filtered diagram of local
`A`-algebras is a local homomorphism: it factors through a stage, where both factors are. -/
theorem isLocalHom_algebraMap_pt (hc : IsColimit c) :
    IsLocalHom (algebraMap A (c.pt : Type v)) := by
  obtain ⟨lam⟩ := IsFiltered.nonempty (C := Λ)
  have := isLocalHom_ι F c hc lam
  refine ⟨fun a ha ↦ ?_⟩
  have h : (c.ι.app lam).hom (algebraMap A (F.obj lam : Type v) a) =
      algebraMap A (c.pt : Type v) a := (c.ι.app lam).hom.commutes a
  rw [← h] at ha
  exact (F.obj lam).isLocalHom.map_nonunit a
    ((isUnit_map_iff (c.ι.app lam).hom.toRingHom _).mp ha)

/-- **The colimit of a filtered diagram in the category `C` of Stacks Tag 05MK, as an object of
`C`.** The underlying `A`-algebra is the apex of a colimit cocone of the underlying diagram of
`A`-algebras, which `Mathlib`'s `HasColimits (CommAlgCat A)` provides. -/
def colimitPt (hc : IsColimit c) : LocalAlgCat.{u, v} A where
  carrier := (c.pt : Type v)
  isLocalRing := isLocalRing_pt F c hc
  isLocalHom := isLocalHom_algebraMap_pt F c hc

/-- **The colimit cocone of a filtered diagram in the category `C` of Stacks Tag 05MK.** Its
legs are the legs of the given colimit cocone of `A`-algebras, which are local homomorphisms. -/
def colimitCocone (hc : IsColimit c) : Cocone F where
  pt := colimitPt F c hc
  ι :=
    { app := fun lam ↦ { hom := (c.ι.app lam).hom, isLocal := isLocalHom_ι F c hc lam }
      naturality := fun _ _ f ↦
        LocalAlgCat.Hom.ext (congrArg CommAlgCat.Hom.hom (c.ι.naturality f)) }

/-- `LocalAlgCat.colimitCocone` is a colimit of the underlying diagram of `A`-algebras:
forgetting the local structure returns the cocone it was built from. This is what makes the
hypotheses of `Module.FlatAtPointSituation.isColimitMapCoconeFlatAtPointFunctor` satisfiable. -/
def isColimitMapCoconeColimitCocone (hc : IsColimit c) :
    IsColimit (toCommAlgCat.mapCocone (colimitCocone F c hc)) := hc

end LocalColimit

end LocalAlgCat

namespace Module.FlatAtPointSituation

open LocalAlgCat

variable {S : FlatAtPointSituation.{u, v, w}} {Λ : Type y} [Category.{z} Λ] [IsFiltered Λ]
  (F : Λ ⥤ LocalAlgCat.{u, x} S.A) (τ : Cocone F) [UnivLE.{y, x}] [UnivLE.{z, x}]

omit [UnivLE.{y, x}] [UnivLE.{z, x}] in
/-- Two witnesses of a value of the functor `F_lf` of Stacks Tag 05MM are equal: the value is
`PLift` of a proposition. -/
theorem flatAtPointFunctor_obj_elim {R : LocalAlgCat.{u, x} S.A}
    (a b : S.flatAtPointFunctor.obj R) : a = b := by
  obtain ⟨a⟩ := a
  obtain ⟨b⟩ := b
  rfl

/-- **Stacks Project, Tag 05MN part (2), the descent step.** If `A → B` is essentially of finite
presentation and `M` is a finitely presented `B`-module, and the flatness condition of
Stacks Tag 05ML holds over the apex of a filtered colimit of local `A`-algebras, then it already
holds over one of the stages.

This is Stacks Tag 05LT, `Module.exists_isFlatAtPrimesOver_of_isColimit`, for the compatible
family of maximal ideals of the stages: their supremum in the apex is the maximal ideal of the
apex, which is `LocalAlgCat.iSup_map_maximalIdeal_eq`. -/
theorem exists_condition_of_isColimit
    (hS : (algebraMap S.A S.B).EssentiallyOfFinitePresentation)
    [Module.FinitePresentation S.B S.M]
    (hτ : IsColimit (toCommAlgCat.mapCocone τ))
    (h : S.Condition τ.pt) :
    ∃ lam, S.Condition (F.obj lam) := by
  have hstage : ∀ lam : Λ, IsLocalRing ((F ⋙ toCommAlgCat).obj lam : Type x) := fun lam ↦
    inferInstanceAs (IsLocalRing (F.obj lam : Type x))
  have hpt : IsLocalRing ((toCommAlgCat.mapCocone τ).pt : Type x) :=
    inferInstanceAs (IsLocalRing (τ.pt : Type x))
  have hι : ∀ lam : Λ, IsLocalHom ((toCommAlgCat.mapCocone τ).ι.app lam).hom.toRingHom :=
    fun lam ↦ (τ.ι.app lam).isLocal
  have hsup : (⨆ lam, Ideal.map ((toCommAlgCat.mapCocone τ).ι.app lam).hom.toRingHom
        (maximalIdeal ((F ⋙ toCommAlgCat).obj lam : Type x))) =
      maximalIdeal ((toCommAlgCat.mapCocone τ).pt : Type x) :=
    iSup_map_maximalIdeal_eq _ hι fun t ↦ CommAlgCat.exists_app_eq hτ t
  refine Module.exists_isFlatAtPrimesOver_of_isColimit (R := S.A) (S := S.B) (M := S.M)
    (maximalIdeal S.B) hS (F ⋙ toCommAlgCat) (toCommAlgCat.mapCocone τ) hτ
    (fun lam ↦ maximalIdeal ((F ⋙ toCommAlgCat).obj lam : Type x))
    (fun {lam mu} f ↦ ?_) ?_
  · have : IsLocalHom ((F ⋙ toCommAlgCat).map f).hom.toRingHom := (F.map f).isLocal
    exact IsLocalRing.map_maximalIdeal_le _
  · exact Eq.mpr (congrArg (fun I : Ideal ((toCommAlgCat.mapCocone τ).pt : Type x) ↦
      Module.IsFlatAtPrimesOver (R := S.A) (S := S.B) (M := S.M) (maximalIdeal S.B)
        ((toCommAlgCat.mapCocone τ).pt : Type x) I) hsup) h

/-- **Stacks Project, Tag 05MN part (2)**, as an equivalence: the flatness condition of
Stacks Tag 05ML holds over the apex of a filtered colimit of local `A`-algebras exactly when it
holds at one of the stages. The easy direction is base-change stability,
`Module.FlatAtPointSituation.condition_of_hom`.

Beyond the hypotheses of the source nothing is assumed about the colimit: that it is computed on
the underlying sets, which is what Stacks Tag 05LT needs, is proved in
`Stacks.CommAlgCat.forget_preservesFilteredColimitsOfSize`. The two `UnivLE` hypotheses are the
size condition that result carries, namely that the index category be no larger than the
algebras; a directed system in the sense of the source is indexed by a set and satisfies it. -/
@[stacks 05MN "limit_preserving"]
theorem condition_colimit_iff
    (hS : (algebraMap S.A S.B).EssentiallyOfFinitePresentation)
    [Module.FinitePresentation S.B S.M]
    (hτ : IsColimit (toCommAlgCat.mapCocone τ)) :
    S.Condition τ.pt ↔ ∃ lam, S.Condition (F.obj lam) :=
  ⟨exists_condition_of_isColimit F τ hS hτ,
    fun ⟨lam, h⟩ ↦ S.condition_of_hom (τ.ι.app lam) h⟩

/-- **Stacks Project, Tag 05MN part (2).** If `A → B` is essentially of finite presentation and
`M` is a `B`-module of finite presentation, then the functor `F_lf` of Stacks Tag 05MM is limit
preserving: for a directed system `{A_i}` of objects of the category `C` of Stacks Tag 05MK,
`F_lf(colim A_i) = colim F_lf(A_i)`.

The colimit of the system is read off the underlying system of `A`-algebras; it does lie in `C`,
by `LocalAlgCat.isLocalRing_pt_of_isColimit` and `LocalAlgCat.isLocalHom_ι_of_isColimit`. The
statement is that the induced cocone of sets is a colimit, which by
`CategoryTheory.Limits.Types.FilteredColimit.isColimitOf` amounts to the descent statement
`Module.FlatAtPointSituation.exists_condition_of_isColimit`, every value of `F_lf` having at
most one element.

That the colimit of `A`-algebras is computed on the underlying sets is not assumed but proved,
in `Stacks.CommAlgCat.forget_preservesFilteredColimitsOfSize`; the two `UnivLE` hypotheses are
the size condition it carries, that the index category of the directed system be no larger than
the algebras. -/
@[stacks 05MN "limit_preserving"]
noncomputable def isColimitMapCoconeFlatAtPointFunctor
    (hS : (algebraMap S.A S.B).EssentiallyOfFinitePresentation)
    [Module.FinitePresentation S.B S.M]
    (hτ : IsColimit (toCommAlgCat.mapCocone τ)) :
    IsColimit (S.flatAtPointFunctor.mapCocone τ) :=
  Types.FilteredColimit.isColimitOf _ _
    (fun h ↦ by
      obtain ⟨lam, hlam⟩ := exists_condition_of_isColimit F τ hS hτ h.down
      exact ⟨lam, PLift.up hlam, flatAtPointFunctor_obj_elim _ _⟩)
    (fun lam mu _ _ _ ↦
      ⟨IsFiltered.max lam mu, IsFiltered.leftToMax lam mu, IsFiltered.rightToMax lam mu,
        flatAtPointFunctor_obj_elim _ _⟩)

end Module.FlatAtPointSituation

end
