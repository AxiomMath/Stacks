module

public import Mathlib.AlgebraicGeometry.Fiber
public import StacksFrontier.AlgebraicGeometry.ChowFiniteType.ModuleSupport
public import StacksFrontier.AlgebraicGeometry.Curves.GenusCurve.BaseChange
public import StacksFrontier.AlgebraicGeometry.F6Rank136.AtWorstNodalDescentAlongLimit
public import StacksFrontier.AlgebraicGeometry.Limits.AffineNoetherianApproximation
public import StacksFrontier.AlgebraicGeometry.Limits.DescendingMorphisms.Smooth
public import StacksFrontier.AlgebraicGeometry.Morphisms.SmoothMorphisms.Basic
public import StacksFrontier.AlgebraicGeometry.ObjectDescent.Basic
public import StacksFrontier.AlgebraicGeometry.Picard.HilbertSchemeSmoothness
public import StacksFrontier.AlgebraicGeometry.Stacks.ModuliEllipticCurvesGluing
public import StacksFrontier.AlgebraicGeometry.Stacks.WeierstrassFamily

/-!
# Local Weierstrass equations: reduction to a Noetherian base

An elliptic curve `(E, f, 0)` over a scheme `S` has a *local Weierstrass equation* at a point
`s ∈ S` when, over some open neighbourhood `U` of `s`, it is the restriction of the Weierstrass
family along a morphism `U ⟶ W`. This file reduces the existence of local Weierstrass equations
for all elliptic curves to the case of a Noetherian affine base, and there to the points at which
the fibre is a curve of genus one; it is the input that construction needs, since the cohomology
and base change arguments behind it are Noetherian.

The reduction is Noetherian approximation. Near `s` the base may be taken affine. An affine
scheme is the limit of the spectra of its finitely generated subrings
(`AlgebraicGeometry.exists_limitNoetherianSituation_of_isAffine`); a family of finite
presentation over the limit is a base change from a stage (Stacks 01ZM), its section comes from a
section at a later stage (Stacks 01ZC), and properness (Stacks 081F), smoothness (Stacks 0C0C) and
the fibre dimension (through syntomicity of relative dimension one) all hold at a later stage.
The genus-one conditions on the fibre at `s` are those at its image, since the dimensions of the
cohomology of the structure sheaf of a proper scheme over a field do not change under extension
of the field (Stacks 0BY9).

## Main definitions

* `AlgebraicGeometry.ModuliEllipticCurves.HasLocalComparison`: near a point, a family is a
  restriction of a fixed family.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.IsGenusOneAt`: the genus-one conditions
  on the fibre at a point.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.Model`: a presentation of a family as a
  base change of a family over another base.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.LocalWeierstrassAt` and
  `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.LocalWeierstrassNoetherian`: the local
  Weierstrass equation at a point, and the statement of its existence over Noetherian affine
  bases.

## Main results

* `AlgebraicGeometry.ModuliEllipticCurves.HasLocalComparison.of_restrict` and
  `AlgebraicGeometry.ModuliEllipticCurves.HasLocalComparison.of_isPullback`: local comparisons
  are transported along restriction to an open and along base change.
* `AlgebraicGeometry.ModuliEllipticCurves.PointedFamily.isGenusOneAt_iff_of_isPullback`: the
  genus-one conditions are invariant under base change.
* `AlgebraicGeometry.ModuliEllipticCurves.exists_noetherian_model`: a family over an affine base,
  proper and smooth of relative dimension one, is a base change of such a family over a
  Noetherian affine base.
* `AlgebraicGeometry.ModuliEllipticCurves.Weierstrass.localWeierstrassAt_of_noetherian`: the
  reduction.

## References

* [Stacks Project, Tag 072S](https://stacks.math.columbia.edu/tag/072S)
* [Stacks Project, Tag 01ZM](https://stacks.math.columbia.edu/tag/01ZM)
* [Stacks Project, Tag 081F](https://stacks.math.columbia.edu/tag/081F)
* [Stacks Project, Tag 0C0C](https://stacks.math.columbia.edu/tag/0C0C)
* [Stacks Project, Tag 0BY9](https://stacks.math.columbia.edu/tag/0BY9)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.ModuliEllipticCurves

variable {W S B : Scheme.{u}}

/-! ### Local comparisons with a fixed family -/

/-- The family `E` over `S` is, near the point `s`, a restriction of the family `F` over `W`:
there are an open `U ∋ s` and a triple `(a, ι_U, α)` identifying `E|_U` with the pullback of `F`
along some `a : U ⟶ W`. -/
def HasLocalComparison (F : PointedFamily W) (E : PointedFamily S) (s : S) : Prop :=
  ∃ U : S.Opens, s ∈ U ∧ ∃ x : Comparison F E U, x.snd = U.ι

namespace HasLocalComparison

variable {F : PointedFamily W} {E : PointedFamily S}

/-- A local comparison of the restriction of `E` to an open `V` is a local comparison of `E`. -/
theorem of_restrict (V : S.Opens) (v : V.toScheme)
    (h : HasLocalComparison F (E.pullback V.ι) v) : HasLocalComparison F E (V.ι v) := by
  obtain ⟨U', hvU', x', hx'⟩ := h
  have hrange : Set.range (V.ι ''ᵁ U').ι = Set.range (U'.ι ≫ V.ι) := by
    rw [Scheme.Opens.range_ι, Scheme.Hom.comp_base, TopCat.coe_comp, Set.range_comp,
      Scheme.Opens.range_ι]
    rfl
  let e := IsOpenImmersion.isoOfRangeEq (V.ι ''ᵁ U').ι (U'.ι ≫ V.ι) hrange
  refine ⟨V.ι ''ᵁ U', ⟨v, hvU', rfl⟩,
    (Comparison.toRestrictSnd V.ι x').baseChange e.hom, ?_⟩
  rw [Comparison.baseChange_snd, Comparison.toRestrictSnd_snd, hx',
    IsOpenImmersion.isoOfRangeEq_hom_fac]

/-- A local comparison transported along base change: if `E` is the pullback of a family `E₀`
over `B` along `π : S ⟶ B`, presented by a cartesian square compatible with the sections, then a
local comparison of `E₀` at `π s` gives one of `E` at `s`. -/
theorem of_isPullback {E₀ : PointedFamily B} (π : S ⟶ B) (q : E.total ⟶ E₀.total)
    (hq : IsPullback q E.map E₀.map π) (hz : E.zero ≫ q = π ≫ E₀.zero) (s : S)
    (h : HasLocalComparison F E₀ (π s)) : HasLocalComparison F E s := by
  obtain ⟨U₀, hsU₀, x₀, hx₀⟩ := h
  let e : FamilyIso E (E₀.pullback π) :=
    { iso := hq.isoPullback
      iso_map := IsPullback.isoPullback_hom_snd _
      zero_iso := Limits.pullback.hom_ext (by
          rw [Category.assoc, IsPullback.isoPullback_hom_fst, hz]
          exact (Limits.pullback.lift_fst _ _ _).symm) (by
          rw [Category.assoc, IsPullback.isoPullback_hom_snd, E.zero_map]
          exact (Limits.pullback.lift_snd _ _ _).symm) }
  let U : S.Opens := π ⁻¹ᵁ U₀
  let y := x₀.baseChange (π ∣_ U₀)
  have hb : y.snd = U.ι ≫ π := by
    rw [Comparison.baseChange_snd, hx₀, morphismRestrict_ι]
  refine ⟨U, hsU₀, Comparison.ofFamilyIso y.fst U.ι
    ((y.familyIso.trans (E₀.pullbackPullbackIso π U.ι hb).symm).trans (e.pullback U.ι).symm),
    rfl⟩

/-- A local comparison of the restriction of `E` along an open immersion `j : T ⟶ S` at `t` is a
local comparison of `E` at `j t`. -/
theorem of_isOpenImmersion {T : Scheme.{u}} (j : T ⟶ S) [IsOpenImmersion j] (t : T)
    (h : HasLocalComparison F (E.pullback j) t) : HasLocalComparison F E (j t) := by
  let e := IsOpenImmersion.isoOfRangeEq j j.opensRange.ι (by rw [Scheme.Opens.range_ι]; rfl)
  have he : j.opensRange.ι = e.inv ≫ j := by
    rw [Iso.eq_inv_comp, IsOpenImmersion.isoOfRangeEq_hom_fac]
  have h' : HasLocalComparison F (E.pullback j.opensRange.ι) (e.hom t) :=
    of_isPullback e.inv (E.pullbackMap e.inv he) (E.isPullback_pullbackMap e.inv he)
      (E.zero_pullbackMap e.inv he) (e.hom t) (by rwa [Scheme.hom_inv_apply])
  have hj : j.opensRange.ι (e.hom t) = j t := by
    rw [← Scheme.Hom.comp_apply, IsOpenImmersion.isoOfRangeEq_hom_fac]
  exact hj ▸ of_restrict j.opensRange (e.hom t) h'

end HasLocalComparison

/-! ### The genus-one conditions at a point are invariant under base change -/

/-- The dimensions of the cohomology groups of the structure sheaf of a proper scheme over a
field are unchanged by extension of the ground field. -/
theorem finrank_structureSheafCohomology_baseChange (k k' : Type u) [Field k] [Field k']
    [Algebra k k'] {X' X : Scheme.{u}} (g' : X' ⟶ X) (f' : X' ⟶ Spec (.of k'))
    (f : X ⟶ Spec (.of k))
    (h : IsPullback g' f' f (Spec.map (CommRingCat.ofHom (algebraMap k k')))) [IsProper f]
    (i : ℕ) :
    Module.finrank k' (structureSheafCohomology f' i) =
      Module.finrank k (structureSheafCohomology f i) := by
  calc
    Module.finrank k' (structureSheafCohomology f' i)
        = Module.finrank k' (cohomologyOverField k' f'
            (SheafOfModules.unit X'.ringCatSheaf) i) :=
      (structureSheafCohomologyIsoCohomologyOverField k' f' i).toLinearEquiv.finrank_eq
    _ = Module.finrank k' (cohomologyOverField k' f'
          ((Scheme.Modules.pullback g').obj (SheafOfModules.unit X.ringCatSheaf)) i) :=
      (finrank_cohomologyOverField_eq_of_iso k' f' (Scheme.Modules.pullbackUnitIso g') i).symm
    _ = Module.finrank k (cohomologyOverField k f (SheafOfModules.unit X.ringCatSheaf) i) :=
      finrank_cohomologyOverField_baseChange_field k k' g' f' f h _ i
    _ = Module.finrank k (structureSheafCohomology f i) :=
      (structureSheafCohomologyIsoCohomologyOverField k f i).toLinearEquiv.finrank_eq.symm

/-- The genus-one conditions on the fibre of a family at a point: one-dimensional `H⁰` and `H¹`
of the structure sheaf of the fibre over the residue field. -/
def PointedFamily.IsGenusOneAt (E : PointedFamily S) (s : S) : Prop :=
  Module.finrank (S.residueField s)
      (structureSheafCohomology (R := S.residueField s) (E.map.fiberToSpecResidueField s) 0) = 1 ∧
    genus (E.map.fiberToSpecResidueField s) = 1

/-- The genus-one conditions at a point are invariant along a cartesian square: if `E` is a base
change of `E₀` along `π`, then `E` satisfies them at `s` exactly when `E₀` does at `π s`. -/
theorem PointedFamily.isGenusOneAt_iff_of_isPullback {E : PointedFamily S} {E₀ : PointedFamily B}
    (π : S ⟶ B) (q : E.total ⟶ E₀.total) (hq : IsPullback q E.map E₀.map π) [IsProper E₀.map]
    (s : S) : E.IsGenusOneAt s ↔ E₀.IsGenusOneAt (π s) := by
  let : Algebra (B.residueField (π s)) (S.residueField s) := (π.residueFieldMap s).hom.toAlgebra
  have hfib' : IsPullback _ (E.map.fiberToSpecResidueField s) (E₀.map.fiberToSpecResidueField (π s))
      (Spec.map (CommRingCat.ofHom (algebraMap (B.residueField (π s)) (S.residueField s)))) :=
    isPullback_fiberToSpecResidueField_of_isPullback hq s
  have : IsProper (E₀.map.fiberToSpecResidueField (π s)) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback E₀.map (B.fromSpecResidueField (π s))) ‹_›
  have h₀ := finrank_structureSheafCohomology_baseChange (B.residueField (π s))
    (S.residueField s) _ _ _ hfib' 0
  have h₁ := genus_baseChange (B.residueField (π s)) (S.residueField s) _ _ _ hfib'
  exact ⟨fun h => ⟨h₀.symm.trans h.1, h₁.symm.trans h.2⟩,
    fun h => ⟨h₀.trans h.1, h₁.trans h.2⟩⟩

/-! ### A Noetherian model of a family over an affine base -/

/-- A property of morphisms respecting isomorphisms holds for the base change, in the `Over`
idiom, of the structure morphism of `X₀` along `g` exactly when it holds for the second
projection `X₀ ×_{B,g} B' ⟶ B'`. -/
theorem overPullback_structure_iff (P : MorphismProperty Scheme.{u}) [P.RespectsIso]
    {B B' : Scheme.{u}} (g : B' ⟶ B) (X₀ : Over B) :
    P ((Over.pullback g).map (Over.homMk X₀.hom (by simp) : X₀ ⟶ Over.mk (𝟙 B))).left ↔
      P (Limits.pullback.snd X₀.hom g) := by
  have h : ((Over.pullback g).map (Over.homMk X₀.hom (by simp) : X₀ ⟶ Over.mk (𝟙 B))).left ≫
      Limits.pullback.snd (𝟙 B) g = Limits.pullback.snd X₀.hom g :=
    Over.w ((Over.pullback g).map (Over.homMk X₀.hom (by simp) : X₀ ⟶ Over.mk (𝟙 B)))
  rw [← h]
  exact (MorphismProperty.cancel_right_of_respectsIso P _ (Limits.pullback.snd (𝟙 B) g)).symm

/-- A model of a pointed family `E` over `S`: a pointed family over `B` together with a cartesian
square exhibiting `E` as its base change along `π : S ⟶ B`, compatibly with the sections. -/
structure PointedFamily.Model (E : PointedFamily S) (B : Scheme.{u}) where
  /-- The morphism to the base of the model. -/
  π : S ⟶ B
  /-- The model family. -/
  family : PointedFamily B
  /-- The projection from `E` to the model. -/
  q : E.total ⟶ family.total
  /-- The square formed by `q`, the two structure morphisms and `π` is cartesian. -/
  isPullback : IsPullback q E.map family.map π
  /-- The projection carries the section of `E` to the section of the model. -/
  zero_q : E.zero ≫ q = π ≫ family.zero

namespace PointedFamily.Model

variable {E : PointedFamily S}

/-- The base change of a model along a morphism of bases through which `π` factors. -/
def pullback (M : E.Model B) {B' : Scheme.{u}} (g : B' ⟶ B) (π' : S ⟶ B') (hπ : π' ≫ g = M.π) :
    E.Model B' where
  π := π'
  family := M.family.pullback g
  q := Limits.pullback.lift M.q (E.map ≫ π') (by rw [Category.assoc, hπ, M.isPullback.w])
  isPullback := by
    refine IsPullback.of_right ?_ (Limits.pullback.lift_snd _ _ _)
      (IsPullback.of_hasPullback M.family.map g)
    rw [Limits.pullback.lift_fst, hπ]
    exact M.isPullback
  zero_q := by
    refine Limits.pullback.hom_ext ?_ ?_
    · rw [Category.assoc, Limits.pullback.lift_fst, M.zero_q, Category.assoc,
        Limits.pullback.lift_fst, ← Category.assoc, hπ]
    · rw [Category.assoc, Limits.pullback.lift_snd, ← Category.assoc, E.zero_map,
        Category.id_comp, Category.assoc, Limits.pullback.lift_snd, Category.comp_id]

/-- A family with a proper model is proper. -/
theorem isProper_of_isProper (M : E.Model B) [IsProper M.family.map] : IsProper E.map :=
  MorphismProperty.IsStableUnderBaseChange.of_isPullback M.isPullback ‹_›

/-- A property of morphisms stable under base change and respecting isomorphisms holds for the
base change, in the `Over` idiom, of the structure morphism of the model to the limit as soon as
it holds for `E`. -/
theorem overPullback_iff (M : E.Model B) (P : MorphismProperty Scheme.{u}) [P.RespectsIso] :
    P ((Over.pullback M.π).map (Over.homMk (Over.mk M.family.map).hom (by simp) :
        Over.mk M.family.map ⟶ Over.mk (𝟙 B))).left ↔ P E.map := by
  rw [overPullback_structure_iff P M.π (Over.mk M.family.map)]
  change P (Limits.pullback.snd M.family.map M.π) ↔ P E.map
  rw [← M.isPullback.isoPullback_hom_snd]
  exact (MorphismProperty.cancel_left_of_respectsIso P _ _).symm

end PointedFamily.Model

section Approximation

open Opposite

variable {J : Type u} [Preorder J] [Nonempty J] [IsDirected J (· ≤ ·)]
  (D : LimitNoetherianSituation.{u, u} J)

/-- The first step of the approximation: a model of `E`, without any property, at some stage of a
Noetherian approximation of the base. -/
theorem exists_model_stage (E : PointedFamily D.limitScheme) (hE : FinitePresentation E.map)
    (hft : ∀ i : J, LocallyOfFiniteType (terminal.from (D.system.obj (op i)))) :
    ∃ (j : Jᵒᵖ) (M : E.Model (D.system.obj j)), M.π = D.limitCone.π.app j ∧
      FinitePresentation M.family.map := by
  have htr : ∀ {i j : Jᵒᵖ} (g : i ⟶ j), IsAffineHom (D.system.map g) :=
    fun g => D.transition_affine g
  have hn : ∀ i : Jᵒᵖ, IsNoetherian (D.system.obj i) := fun i => D.noetherian i.unop
  have hlft : ∀ i : Jᵒᵖ, LocallyOfFiniteType (terminal.from (D.system.obj i)) :=
    fun i => hft i.unop
  let c := D.limitCone
  obtain ⟨i, Xi, hXi, ⟨φ⟩⟩ := LimitFPObjectDescent.exists_model_of_finitePresentation D.system c
    D.isLimit (Over.mk E.map) hE
  have : LocallyOfFinitePresentation Xi.hom := hXi.1
  have : LocallyOfFinitePresentation (terminal.from Xi.left) := by
    rw [← terminal.comp_from Xi.hom]
    infer_instance
  have hφ : φ.hom.left ≫ Limits.pullback.snd Xi.hom (c.π.app i) = E.map := Over.w φ.hom
  -- the section of `E`, read in the model at stage `i`
  let a : c.pt ⟶ Xi.left := E.zero ≫ φ.hom.left ≫ Limits.pullback.fst Xi.hom (c.π.app i)
  have ha : a ≫ Xi.hom = c.π.app i := by
    simp only [a, Category.assoc, Limits.pullback.condition, reassoc_of% hφ,
      reassoc_of% E.zero_map]
  let t : D.system ⟶ (Functor.const Jᵒᵖ).obj (⊤_ Scheme.{u}) :=
    { app := fun _ => terminal.from _, naturality := fun _ _ _ => terminal.hom_ext _ _ }
  obtain ⟨j₁, g₁, hg₁, -⟩ := Scheme.exists_π_app_comp_eq_of_locallyOfFinitePresentation D.system
    t (terminal.from Xi.left) c D.isLimit a (by ext; exact terminal.hom_ext _ _)
  let j₂ := IsCofiltered.min i j₁
  let g₂ : D.system.obj j₂ ⟶ Xi.left := D.system.map (IsCofiltered.minToRight i j₁) ≫ g₁
  obtain ⟨j, e₂, he₂⟩ := Scheme.exists_hom_comp_eq_comp_of_locallyOfFiniteType D.system t
    (terminal.from (D.system.obj i)) c D.isLimit (g₂ ≫ Xi.hom)
    (D.system.map (IsCofiltered.minToLeft i j₁)) (terminal.hom_ext _ _) (terminal.hom_ext _ _)
    (by
      simp only [g₂, Category.assoc]
      rw [← Category.assoc (c.π.app j₂), c.w, ← Category.assoc, hg₁, ha, c.w])
  let e : j ⟶ i := e₂ ≫ IsCofiltered.minToLeft i j₁
  have hze : (D.system.map e₂ ≫ g₂) ≫ Xi.hom = 𝟙 _ ≫ D.system.map e := by
    rw [Category.assoc, he₂, Category.id_comp, ← D.system.map_comp]
  let F : PointedFamily (D.system.obj j) :=
    { total := Limits.pullback Xi.hom (D.system.map e)
      map := Limits.pullback.snd Xi.hom (D.system.map e)
      zero := Limits.pullback.lift (D.system.map e₂ ≫ g₂) (𝟙 _) hze
      zero_map := Limits.pullback.lift_snd _ _ _ }
  have hq : (φ.hom.left ≫ Limits.pullback.fst Xi.hom (c.π.app i)) ≫ Xi.hom =
      (E.map ≫ c.π.app j) ≫ D.system.map e := by
    rw [Category.assoc, Limits.pullback.condition, reassoc_of% hφ, Category.assoc, c.w]
  have hbig : IsPullback (φ.hom.left ≫ Limits.pullback.fst Xi.hom (c.π.app i)) E.map Xi.hom
      (c.π.app i) := by
    have : IsIso φ.hom.left := (Over.forget _).map_isIso φ.hom
    have h₁ : IsPullback φ.hom.left E.map (Limits.pullback.snd Xi.hom (c.π.app i)) (𝟙 _) :=
      IsPullback.of_horiz_isIso ⟨by rw [hφ, Category.comp_id]⟩
    simpa using h₁.paste_horiz (IsPullback.of_hasPullback Xi.hom (c.π.app i)).flip.flip
  refine ⟨j,
    { π := c.π.app j
      family := F
      q := Limits.pullback.lift _ _ hq
      isPullback := by
        refine IsPullback.of_right ?_ (Limits.pullback.lift_snd _ _ _)
          (IsPullback.of_hasPullback Xi.hom (D.system.map e))
        rw [Limits.pullback.lift_fst, c.w]
        exact hbig
      zero_q := by
        refine Limits.pullback.hom_ext ?_ ?_
        · change E.zero ≫ Limits.pullback.lift _ _ hq ≫ Limits.pullback.fst _ _ =
            c.π.app j ≫ Limits.pullback.lift (D.system.map e₂ ≫ g₂) (𝟙 _) hze ≫
              Limits.pullback.fst _ _
          rw [Limits.pullback.lift_fst, Limits.pullback.lift_fst]
          simp only [g₂, ← Category.assoc, c.w]
          exact hg₁.symm.trans (by simp)
        · change E.zero ≫ Limits.pullback.lift _ _ hq ≫ Limits.pullback.snd _ _ =
            c.π.app j ≫ Limits.pullback.lift (D.system.map e₂ ≫ g₂) (𝟙 _) hze ≫
              Limits.pullback.snd _ _
          rw [Limits.pullback.lift_snd, Limits.pullback.lift_snd, reassoc_of% E.zero_map,
            Category.comp_id] }, rfl, ?_⟩
  have : QuasiCompact Xi.hom := hXi.2.1
  have : QuasiSeparated Xi.hom := hXi.2.2
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/-- Three properties stable under base change, holding for the base changes of `f` to three
stages of a Noetherian approximation, hold together for its base change to a common later stage. -/
private theorem exists_stage_overPullback_map (P₁ P₂ P₃ : MorphismProperty Scheme.{u})
    [P₁.IsStableUnderBaseChange] [P₂.IsStableUnderBaseChange] [P₃.IsStableUnderBaseChange]
    {j : Jᵒᵖ} {X Y : Over (D.system.obj j)} (f : X ⟶ Y) {k₁ k₂ k₃ : Jᵒᵖ}
    (g₁ : k₁ ⟶ j) (g₂ : k₂ ⟶ j) (g₃ : k₃ ⟶ j)
    (h₁ : P₁ ((Over.pullback (D.system.map g₁)).map f).left)
    (h₂ : P₂ ((Over.pullback (D.system.map g₂)).map f).left)
    (h₃ : P₃ ((Over.pullback (D.system.map g₃)).map f).left) :
    ∃ (k : Jᵒᵖ) (g : k ⟶ j), P₁ ((Over.pullback (D.system.map g)).map f).left ∧
      P₂ ((Over.pullback (D.system.map g)).map f).left ∧
      P₃ ((Over.pullback (D.system.map g)).map f).left := by
  have later (P : MorphismProperty Scheme.{u}) [P.IsStableUnderBaseChange] {k k' : Jᵒᵖ}
      (g : k' ⟶ j) (a : k ⟶ k') (h : P ((Over.pullback (D.system.map g)).map f).left) :
      P ((Over.pullback (D.system.map (a ≫ g))).map f).left := by
    rw [D.system.map_comp]
    exact overPullback_map_comp P _ _ f h
  let k₁₂ := IsCofiltered.min k₁ k₂
  let a₁ : IsCofiltered.min k₁₂ k₃ ⟶ k₁ :=
    IsCofiltered.minToLeft k₁₂ k₃ ≫ IsCofiltered.minToLeft k₁ k₂
  let a₂ : IsCofiltered.min k₁₂ k₃ ⟶ k₂ :=
    IsCofiltered.minToLeft k₁₂ k₃ ≫ IsCofiltered.minToRight k₁ k₂
  refine ⟨_, a₁ ≫ g₁, later P₁ g₁ a₁ h₁, ?_, ?_⟩
  · rw [show a₁ ≫ g₁ = a₂ ≫ g₂ from Subsingleton.elim _ _]
    exact later P₂ g₂ a₂ h₂
  · rw [show a₁ ≫ g₁ = IsCofiltered.minToRight k₁₂ k₃ ≫ g₃ from Subsingleton.elim _ _]
    exact later P₃ g₃ _ h₃

/-- Properness, smoothness and the fibre dimension of a family descend from the limit of a
Noetherian approximation to a later stage of a model. -/
theorem exists_model_isProper_smoothOfRelativeDimension (E : PointedFamily D.limitScheme)
    [IsProper E.map] [SmoothOfRelativeDimension 1 E.map] (j : Jᵒᵖ) (M : E.Model (D.system.obj j))
    (hM : M.π = D.limitCone.π.app j) (hfp : FinitePresentation M.family.map) :
    ∃ (k : Jᵒᵖ) (M' : E.Model (D.system.obj k)),
      IsProper M'.family.map ∧ SmoothOfRelativeDimension 1 M'.family.map := by
  have htr : ∀ {i j : Jᵒᵖ} (g : i ⟶ j), IsAffineHom (D.system.map g) :=
    fun g => D.transition_affine g
  have hn : ∀ i : Jᵒᵖ, IsNoetherian (D.system.obj i) := fun i => D.noetherian i.unop
  let c := D.limitCone
  let X₀ : Over (D.system.obj j) := Over.mk M.family.map
  let f₀ : X₀ ⟶ Over.mk (𝟙 (D.system.obj j)) := Over.homMk X₀.hom (by simp)
  have : LocallyOfFinitePresentation f₀.left := hfp.1
  have : QuasiCompact M.family.map := hfp.2.1
  have : QuasiSeparated M.family.map := hfp.2.2
  have : CompactSpace X₀.left := QuasiCompact.compactSpace_of_compactSpace M.family.map
  have : QuasiSeparatedSpace X₀.left := quasiSeparatedSpace_of_quasiSeparated M.family.map
  have : CompactSpace (Over.mk (𝟙 (D.system.obj j))).left :=
    inferInstanceAs (CompactSpace (D.system.obj j))
  have : QuasiSeparatedSpace (Over.mk (𝟙 (D.system.obj j))).left :=
    inferInstanceAs (QuasiSeparatedSpace (D.system.obj j))
  have hlim (P : MorphismProperty Scheme.{u}) [P.RespectsIso] (hP : P E.map) :
      P ((Over.pullback (c.π.app j)).map f₀).left := by
    have := (M.overPullback_iff P).2 hP
    rwa [hM] at this
  have : Smooth E.map := SmoothOfRelativeDimension.smooth 1 E.map
  have hsynbc : MorphismProperty.IsStableUnderBaseChange
      (@SyntomicOfRelativeDimension 1 : MorphismProperty Scheme.{u}) :=
    syntomicOfRelativeDimension_isStableUnderBaseChange 1
  have : MorphismProperty.RespectsIso
      (@SyntomicOfRelativeDimension 1 : MorphismProperty Scheme.{u}) := hsynbc.respectsIso
  have : MorphismProperty.RespectsIso (@Smooth : MorphismProperty Scheme.{u}) :=
    MorphismProperty.IsStableUnderBaseChange.respectsIso
  have : IsProper ((Over.pullback (c.π.app j)).map f₀).left := hlim @IsProper inferInstance
  have : Smooth ((Over.pullback (c.π.app j)).map f₀).left := hlim @Smooth inferInstance
  obtain ⟨k₁, g₁, h₁⟩ := exists_isProper_baseChange_of_isLimit D.system c j D.isLimit X₀ _ f₀
  obtain ⟨k₂, g₂, h₂⟩ := exists_smooth_baseChange_of_smooth_limitBaseChange D.system c j X₀ _ f₀
    D.isLimit
  obtain ⟨k₃, g₃, h₃⟩ := exists_syntomicOfRelativeDimension_baseChange_of_limitBaseChange 1
    D.system c j X₀ _ f₀ D.isLimit
    (hlim (@SyntomicOfRelativeDimension 1) ⟨syntomic_of_smooth E.map,
      fiberDimensionAt_eq_of_smoothOfRelativeDimension E.map 1⟩)
  obtain ⟨k, gk, hp, hs, hd⟩ := exists_stage_overPullback_map D @IsProper @Smooth
    (@SyntomicOfRelativeDimension 1) f₀ g₁ g₂ g₃ h₁ h₂ h₃
  have hp' := (overPullback_structure_iff @IsProper (D.system.map gk) X₀).1 hp
  have hs' := (overPullback_structure_iff @Smooth (D.system.map gk) X₀).1 hs
  have hd' := (overPullback_structure_iff (@SyntomicOfRelativeDimension 1)
    (D.system.map gk) X₀).1 hd
  refine ⟨k, M.pullback (D.system.map gk) (c.π.app k) (by rw [hM]; exact c.w gk), hp', ?_⟩
  have : Smooth (M.pullback (D.system.map gk) (c.π.app k)
      (by rw [hM]; exact c.w gk)).family.map := hs'
  exact Stacks.Smooth.smoothOfRelativeDimension_of_fiberDimensionAt_eq _ 1 hd'.2

end Approximation

/-- **A family over an affine base, proper and smooth of relative dimension one with a section,
is a base change of such a family over a Noetherian affine base.** The Noetherian base is a stage
of the Noetherian approximation of the affine base by spectra of finitely generated subrings. -/
theorem exists_noetherian_model {S : Scheme.{u}} [IsAffine S] (E : PointedFamily S)
    [IsProper E.map] [SmoothOfRelativeDimension 1 E.map] :
    ∃ (B : Scheme.{u}) (_ : IsAffine B) (_ : IsNoetherian B) (M : E.Model B),
      IsProper M.family.map ∧ SmoothOfRelativeDimension 1 M.family.map := by
  obtain ⟨J, _, _, _, D, hD, haff, hft⟩ := exists_limitNoetherianSituation_of_isAffine S
  subst hD
  have : Smooth E.map := SmoothOfRelativeDimension.smooth 1 E.map
  have hE : FinitePresentation E.map := ⟨inferInstance, inferInstance, inferInstance⟩
  obtain ⟨j, M, hM, hfp⟩ := exists_model_stage D E hE hft
  obtain ⟨k, M', hp, hs⟩ := exists_model_isProper_smoothOfRelativeDimension D E j M hM hfp
  exact ⟨_, haff k.unop, D.noetherian k.unop, M', hp, hs⟩

/-- The local Weierstrass equation at a point: near `s` the family `E` is a restriction of the
Weierstrass family. -/
abbrev Weierstrass.LocalWeierstrassAt (E : PointedFamily S) (s : S) : Prop :=
  HasLocalComparison Weierstrass.family.{u} E s

/-- The local Weierstrass equation over Noetherian affine bases, at a point where the fibre is a
curve of genus one: the statement which the construction of the Weierstrass equation proves. -/
def Weierstrass.LocalWeierstrassNoetherian : Prop :=
  ∀ {S : Scheme.{u}} [IsAffine S] [IsNoetherian S] (E : PointedFamily S), IsProper E.map →
    SmoothOfRelativeDimension 1 E.map → ∀ s : S, E.IsGenusOneAt s → LocalWeierstrassAt E s

/-- The pullback of a proper, smooth family of relative dimension one along `j` is again such a
family, and it satisfies the genus-one conditions at `t` as soon as `E` does at `j t`. -/
private theorem pullback_isProper_smooth_isGenusOneAt {T : Scheme.{u}} (E : PointedFamily S)
    (j : T ⟶ S) (hproper : IsProper E.map) (hsmooth : SmoothOfRelativeDimension 1 E.map) (t : T)
    (hg : E.IsGenusOneAt (j t)) :
    IsProper (E.pullback j).map ∧ SmoothOfRelativeDimension 1 (E.pullback j).map ∧
      (E.pullback j).IsGenusOneAt t :=
  ⟨MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (IsPullback.of_hasPullback E.map j) hproper,
    (smoothOfRelativeDimension_isStableUnderBaseChange (n := 1)).of_isPullback
      (IsPullback.of_hasPullback E.map j) hsmooth,
    (PointedFamily.isGenusOneAt_iff_of_isPullback j (Limits.pullback.fst E.map j)
      (IsPullback.of_hasPullback E.map j) t).2 hg⟩

/-- **Reduction of the local Weierstrass equation to a Noetherian base.** If every family over a
Noetherian affine base which is proper and smooth of relative dimension one has a local
Weierstrass equation at the points where its fibre has genus one, then every elliptic curve has a
local Weierstrass equation at every point of its base. -/
theorem Weierstrass.localWeierstrassAt_of_noetherian (H : LocalWeierstrassNoetherian.{u})
    (E : PointedFamily S) (hE : E.IsElliptic) (s : S) : LocalWeierstrassAt E s := by
  obtain ⟨hproper, hsmooth, hfib⟩ := hE
  obtain ⟨V', hV, hsV, -⟩ :=
    exists_isAffineOpen_mem_and_subset (show s ∈ (⊤ : S.Opens) from trivial)
  have : IsAffine V'.toScheme := hV
  let EV := E.pullback V'.ι
  let v : V'.toScheme := ⟨s, hsV⟩
  have hv : V'.ι v = s := rfl
  obtain ⟨_, _, hgV⟩ := pullback_isProper_smooth_isGenusOneAt E V'.ι hproper hsmooth v
    (by rw [hv]; exact hfib s)
  obtain ⟨B, _, _, M, hMp, hMs⟩ := exists_noetherian_model EV
  have hgB : M.family.IsGenusOneAt (M.π v) :=
    (PointedFamily.isGenusOneAt_iff_of_isPullback M.π M.q M.isPullback v).1 hgV
  rw [← hv]
  exact HasLocalComparison.of_restrict V' v
    (HasLocalComparison.of_isPullback M.π M.q M.isPullback M.zero_q v (H M.family hMp hMs _ hgB))

/-- **Reduction of the local Weierstrass equation over Noetherian affine bases to spectra of
Noetherian rings.** An affine scheme is isomorphic to the spectrum of its global sections, and
the local Weierstrass equation is transported along this isomorphism. -/
theorem Weierstrass.localWeierstrassNoetherian_of_spec
    (H : ∀ (A : Type u) [CommRing A] [IsNoetherianRing A] (E : PointedFamily (Spec (.of A))),
      IsProper E.map → SmoothOfRelativeDimension 1 E.map → ∀ x, E.IsGenusOneAt x →
        LocalWeierstrassAt E x) :
    LocalWeierstrassNoetherian.{u} := by
  intro S _ _ E hproper hsmooth s hs
  let j : Spec (.of Γ(S, ⊤)) ⟶ S := S.isoSpec.inv
  let EA := E.pullback j
  have ht : j (S.isoSpec.hom s) = s := Scheme.hom_inv_apply S.isoSpec s
  obtain ⟨hEA, hEA', hg⟩ := pullback_isProper_smooth_isGenusOneAt E j hproper hsmooth _
    (by rwa [ht])
  have : IsNoetherianRing Γ(S, ⊤) :=
    IsLocallyNoetherian.component_noetherian ⟨⊤, isAffineOpen_top S⟩
  rw [← ht]
  exact HasLocalComparison.of_isOpenImmersion j _ (H Γ(S, ⊤) EA hEA hEA' _ hg)


end AlgebraicGeometry.ModuliEllipticCurves

end
