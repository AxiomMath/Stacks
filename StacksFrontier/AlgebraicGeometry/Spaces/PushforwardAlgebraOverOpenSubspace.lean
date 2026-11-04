module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.RestrictScalarsEpiFullyFaithful
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAlgebraAntiEquivalence
public import StacksFrontier.AlgebraicGeometry.Spaces.AlgebraSheafIsoOverSubfunctor
public import StacksFrontier.AlgebraicGeometry.Spaces.EtaleCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeOnSiteAffineCharts
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleRingedToposHom

/-!
# The direct image of a space lying over an open subspace only sees that subspace

Let `Y` be an algebraic space over a scheme `S`, let `V ⊆ Y` be an open subspace, and let
`P ⟶ Y` be a representable morphism which factors through `V`.  The direct-image algebra
`P_* 𝒪_P` on the small étale site of `Y` is then determined by its sections over the affine étale
charts of `Y` which factor through `V`: it is separated, and glues, along the presieves of those
charts.  Combined with
`AlgebraicGeometry.Space.AlgebraSheaf.bijective_comp_of_isIsoOver`, a morphism of algebra sheaves
which is an isomorphism over `V` induces a bijection on the morphisms into `P_* 𝒪_P`.  This is the
step `f^{-1}(V) = f_i^{-1}(V)` of the source's proof of Stacks 0GUM, read on points.

## Main definitions

* `AlgebraicGeometry.Space.openPreimageChart`: for an étale chart `U` of `Y`, the chart
  `U ×_Y V`, an open subscheme of `U`, with its inclusion
  `AlgebraicGeometry.Space.openPreimageChartι` into `U`.

## Main results

* `AlgebraicGeometry.Space.range_openPreimageChart_le`: `U ×_Y V` factors through `V`.
* `AlgebraicGeometry.Space.exists_comp_openPreimageChartι`: a chart over `U` which factors through
  `V` factors through `U ×_Y V`.
* `AlgebraicGeometry.Space.isIso_smallBaseChange_map_openPreimageChartι`: when `P ⟶ Y` factors
  through `V`, base change along it identifies `P ×_Y (U ×_Y V)` with `P ×_Y U`.
* `AlgebraicGeometry.Space.bijective_pushforwardAlgebra_map_openPreimageChartι`: when `P ⟶ Y`
  factors through `V`, the sections of `P_* 𝒪_P` over `U` and over `U ×_Y V` agree.
* `AlgebraicGeometry.Space.isSeparatedOn_and_gluesOn_of_factor`: an algebra sheaf is separated
  and glues along presieves which factor through charts with the same sections, on which they
  generate a covering.
* `AlgebraicGeometry.Space.isSeparatedOn_and_gluesOn_pushforwardAlgebra`: `P_* 𝒪_P` is separated,
  and glues, along the affine étale charts factoring through `V`.
* `AlgebraicGeometry.Space.bijective_comp_pushforwardAlgebra_of_isIsoOver`: a morphism of algebra
  sheaves which is an isomorphism over `V` induces a bijection on morphisms into `P_* 𝒪_P`.

## References

* [Stacks Project, Tag 0GUM](https://stacks.math.columbia.edu/tag/0GUM)
* [Stacks Project, Tag 03G8](https://stacks.math.columbia.edu/tag/03G8)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry.Space

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-! ### The open subscheme `U ×_Y V` of a chart -/

section OpenPreimage

variable {B S hS} {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {V : Subfunctor Y}
    (hV : IsOpenImmersion B S hS V.ι)

/-- **The chart `U ×_Y V`** of an étale chart `U` of `Y`: the representative of the base change
of the open immersion `V ⟶ Y` along `U`, an open subscheme of `U`, with the composite to `Y`. -/
def openPreimageChart (U : SmallEtale B S hS Y) : SmallEtale B S hS Y :=
  ⟨CostructuredArrow.mk (yoneda.map (hV.rep.snd U.1.hom) ≫ U.1.hom),
    etale_comp_of_scheme B S hS _ U.1.hom
      (by
        have : AlgebraicGeometry.IsOpenImmersion
            ((BigFppfOver.toScheme B S hS).map (hV.rep.snd U.1.hom)) :=
          hV.property_snd U.1.hom
        infer_instance)
      U.property⟩

/-- The inclusion `U ×_Y V ⟶ U`. -/
def openPreimageChartι (U : SmallEtale B S hS Y) : openPreimageChart hV U ⟶ U :=
  ObjectProperty.homMk (CostructuredArrow.homMk (hV.rep.snd U.1.hom) rfl)

/-- The underlying morphism of schemes of `U ×_Y V ⟶ U` is the projection of the base change to
`U`. -/
@[simp]
theorem openPreimageChartι_hom_left (U : SmallEtale B S hS Y) :
    (openPreimageChartι hV U).hom.left = hV.rep.snd U.1.hom :=
  rfl

/-- The structure morphism of `U ×_Y V` to `Y` is the first projection to `V` followed by the
inclusion `V ⟶ Y`. -/
theorem openPreimageChart_hom (U : SmallEtale B S hS Y) :
    (openPreimageChart hV U).1.hom = hV.rep.fst U.1.hom ≫ V.ι :=
  (hV.rep.w U.1.hom).symm

/-- **`U ×_Y V` factors through `V`.** -/
theorem range_openPreimageChart_le (U : SmallEtale B S hS Y) :
    Subfunctor.range (openPreimageChart hV U).1.hom ≤ V := by
  rw [openPreimageChart_hom]
  refine (Subfunctor.range_comp_le _ _).trans ?_
  rw [Subfunctor.range_ι]

/-- A chart which maps to a chart factoring through `V` factors through `V`. -/
theorem range_le_range_of_hom {W W' : SmallEtale B S hS Y} (g : W' ⟶ W) :
    Subfunctor.range W'.1.hom ≤ Subfunctor.range W.1.hom := by
  rw [← CostructuredArrow.w g.hom]
  exact Subfunctor.range_comp_le _ _

/-- **A chart over `U` which factors through `V` factors through `U ×_Y V`.** -/
theorem exists_comp_openPreimageChartι {U W : SmallEtale B S hS Y} (f : W ⟶ U)
    (hW : Subfunctor.range W.1.hom ≤ V) :
    ∃ f' : W ⟶ openPreimageChart hV U, f' ≫ openPreimageChartι hV U = f := by
  have hi : Subfunctor.lift W.1.hom hW ≫ V.ι = yoneda.map f.hom.left ≫ U.1.hom := by
    rw [Subfunctor.lift_ι]
    exact (CostructuredArrow.w f.hom).symm
  let l := hV.rep.lift (Subfunctor.lift W.1.hom hW) f.hom.left hi
  refine ⟨ObjectProperty.homMk (CostructuredArrow.homMk l ?_), ?_⟩
  · show yoneda.map l ≫ yoneda.map (hV.rep.snd U.1.hom) ≫ U.1.hom = W.1.hom
    rw [← Category.assoc, ← Functor.map_comp, hV.rep.lift_snd]
    exact CostructuredArrow.w f.hom
  · exact ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ (hV.rep.lift_snd _ _ _))

end OpenPreimage

/-! ### Base change along a space lying over `V` -/

section BaseChange

variable {B S hS} {Y : AlgebraicSpaces B S hS} {V : Subfunctor Y.1}
    (hV : IsOpenImmersion B S hS V.ι)

/-- **Base change along a representable `P ⟶ Y` factoring through `V` identifies
`P ×_Y (U ×_Y V)` with `P ×_Y U`**: the base change of the inclusion `U ×_Y V ⟶ U` is an
isomorphism of étale charts of `P`. -/
theorem isIso_smallBaseChange_map_openPreimageChartι {P : AlgebraicSpaces B S hS} (p : P ⟶ Y)
    (hp : yoneda.relativelyRepresentable p.hom) (t : P.1 ⟶ V.toFunctor) (ht : t ≫ V.ι = p.hom)
    (U : SmallEtale B S hS Y.1) :
    IsIso ((smallBaseChange B S hS p hp).map (openPreimageChartι hV U)) := by
  let g : yoneda.obj (hV.rep.pullback U.1.hom) ⟶ Y.1 := yoneda.map (hV.rep.snd U.1.hom) ≫ U.1.hom
  have hφ : hp.fst g ≫ p.hom = yoneda.map (hp.snd g ≫ hV.rep.snd U.1.hom) ≫ U.1.hom := by
    rw [Functor.map_comp, Category.assoc]
    exact hp.w g
  let φ : hp.pullback g ⟶ hp.pullback U.1.hom :=
    hp.lift (hp.fst g) (hp.snd g ≫ hV.rep.snd U.1.hom) hφ
  have hφfst : yoneda.map φ ≫ hp.fst U.1.hom = hp.fst g := hp.lift_fst _ _ _
  have hφsnd : φ ≫ hp.snd U.1.hom = hp.snd g ≫ hV.rep.snd U.1.hom := hp.lift_snd _ _ _
  have hm : (hp.fst U.1.hom ≫ t) ≫ V.ι = yoneda.map (hp.snd U.1.hom) ≫ U.1.hom := by
    rw [Category.assoc, ht]
    exact hp.w U.1.hom
  let m : hp.pullback U.1.hom ⟶ hV.rep.pullback U.1.hom :=
    hV.rep.lift (hp.fst U.1.hom ≫ t) (hp.snd U.1.hom) hm
  have hmfst : yoneda.map m ≫ hV.rep.fst U.1.hom = hp.fst U.1.hom ≫ t := hV.rep.lift_fst _ _ _
  have hmsnd : m ≫ hV.rep.snd U.1.hom = hp.snd U.1.hom := hV.rep.lift_snd _ _ _
  have hψ : hp.fst U.1.hom ≫ p.hom = yoneda.map m ≫ g := by
    rw [← Category.assoc, ← Functor.map_comp, hmsnd]
    exact hp.w U.1.hom
  let ψ : hp.pullback U.1.hom ⟶ hp.pullback g := hp.lift (hp.fst U.1.hom) m hψ
  have hψfst : yoneda.map ψ ≫ hp.fst g = hp.fst U.1.hom := hp.lift_fst _ _ _
  have hψsnd : ψ ≫ hp.snd g = m := hp.lift_snd _ _ _
  have h₁ : ψ ≫ φ = 𝟙 _ := by
    refine hp.hom_ext ?_ ?_ <;> simp [hφfst, hψfst, hφsnd, reassoc_of% hψsnd, hmsnd]
  have h₃ : φ ≫ m = hp.snd g := by
    refine hV.rep.hom_ext ?_ ?_
    · rw [← cancel_mono V.ι, Functor.map_comp, Category.assoc, Category.assoc, Category.assoc,
        ← Category.assoc (yoneda.map m), hmfst, Category.assoc, ht, ← Category.assoc, hφfst,
        hp.w g, hV.rep.w]
    · rw [Category.assoc, hmsnd, hφsnd]
  have h₂ : φ ≫ ψ = 𝟙 _ := by
    refine hp.hom_ext ?_ ?_ <;> simp [hφfst, hψfst, hψsnd, h₃]
  exact ⟨ObjectProperty.homMk (CostructuredArrow.homMk ψ hψfst),
    ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ h₂),
    ObjectProperty.hom_ext _ (CostructuredArrow.hom_ext _ _ h₁)⟩

end BaseChange

/-! ### The direct image of a space lying over `V` -/

section Pushforward

variable {B S hS} {Y : AlgebraicSpaces B S hS} {V : Subfunctor Y.1}
    (hV : IsOpenImmersion B S hS V.ι)

/-- The underlying presheaf of types of a sheaf of commutative rings on the small étale site is a
sheaf of types. -/
theorem isSheaf_typePresheaf (A : AlgebraSheaf.{u, u} B S hS Y.1 Y.2) :
    Presieve.IsSheaf (SmallEtale.topology B S hS Y.1) (A.right.obj ⋙ forget CommRingCat.{u}) :=
  (isSheaf_iff_isSheaf_of_type _ _).1
    (Stacks.NoncommChangeOfRings.Silver.isSheaf_forget_of_isSheaf
      ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        A.right).obj
      ((sheafCompose (SmallEtale.topology B S hS Y.1) (forget₂ CommRingCat.{u} RingCat.{u})).obj
        A.right).property)

variable {P : Over Y} (hP : yoneda.relativelyRepresentable P.hom.hom) (t : P.left.1 ⟶ V.toFunctor)
    (ht : t ≫ V.ι = P.hom.hom)

include hP ht in
/-- **The direct image `P_* 𝒪_P` is unchanged by restriction from a chart `U` to `U ×_Y V`**
when `P ⟶ Y` factors through `V`. -/
theorem bijective_pushforwardAlgebra_map_openPreimageChartι (U : SmallEtale B S hS Y.1) :
    Function.Bijective
      ((pushforwardAlgebra B S hS P).right.obj.map (openPreimageChartι hV U).op).hom := by
  let := (smallBaseChange_isMorphismOfSites B S hS P.hom hP).toIsContinuous
  let e := (smallEtaleRingedToposHom_representableRing B S hS P.hom hP).app
    (smallEtaleRingedTopos B S hS P.left).O
  have hnat := e.hom.hom.naturality (openPreimageChartι hV U).op
  have hiso := isIso_smallBaseChange_map_openPreimageChartι hV P.hom hP t ht U
  have hH : Function.Bijective (((smallBaseChange B S hS P.hom hP).sheafPushforwardContinuous
      CommRingCat.{u} (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS P.left.1)).obj
        (smallEtaleRingedTopos B S hS P.left).O |>.obj.map (openPreimageChartι hV U).op).hom :=
    ConcreteCategory.bijective_of_isIso
      ((smallEtaleRingedTopos B S hS P.left).O.obj.map
        ((smallBaseChange B S hS P.hom hP).map (openPreimageChartι hV U)).op)
  have hcomp : (e.hom.hom.app (op (openPreimageChart hV U))).hom ∘
      ((pushforwardAlgebra B S hS P).right.obj.map (openPreimageChartι hV U).op).hom =
      (((smallBaseChange B S hS P.hom hP).sheafPushforwardContinuous
        CommRingCat.{u} (SmallEtale.topology B S hS Y.1) (SmallEtale.topology B S hS P.left.1)).obj
          (smallEtaleRingedTopos B S hS P.left).O |>.obj.map (openPreimageChartι hV U).op).hom ∘
        (e.hom.hom.app (op U)).hom :=
    funext fun x => by
      have h := congrArg (fun k => k.hom x) hnat
      simp only [CommRingCat.hom_comp] at h
      exact h
  refine (Function.Bijective.of_comp_iff' (ConcreteCategory.bijective_of_isIso
    (e.hom.hom.app (op (openPreimageChart hV U)))) _).1 ?_
  rw [hcomp]
  exact hH.comp (ConcreteCategory.bijective_of_isIso (e.hom.hom.app (op U)))

end Pushforward

/-! ### Separation and glueing along the charts factoring through `V` -/

section Glueing

variable {B S hS} {Y : AlgebraicSpaces B S hS}

/-- **An algebra sheaf is separated and glues along a family of presieves which, on each chart
`U`, factor through a chart `U'` with the same sections and generate a covering of `U'`.** -/
theorem isSeparatedOn_and_gluesOn_of_factor (G : AlgebraSheaf.{u, u} B S hS Y.1 Y.2)
    (R : ∀ U : SmallEtale B S hS Y.1, Presieve U)
    (U' : SmallEtale B S hS Y.1 → SmallEtale B S hS Y.1)
    (ι : ∀ U, U' U ⟶ U) (hbij : ∀ U, Function.Bijective (G.right.obj.map (ι U).op).hom)
    (hfac : ∀ (U W : SmallEtale B S hS Y.1) (f : W ⟶ U), R U f → ∃ k, k ≫ ι U = f)
    (hcov : ∀ U, Sieve.generate (fun W (k : W ⟶ U' U) => R U (k ≫ ι U)) ∈
      SmallEtale.topology B S hS Y.1 (U' U)) :
    G.IsSeparatedOn R ∧ G.GluesOn R := by
  have hsh : ∀ U, Presieve.IsSheafFor (G.right.obj ⋙ forget CommRingCat.{u})
      (fun W (k : W ⟶ U' U) => R U (k ≫ ι U)) := fun U =>
    (Presieve.isSheafFor_iff_generate _).2 (isSheaf_typePresheaf G _ (hcov U))
  refine ⟨fun U s t h => (hbij U).1 ((hsh U).isSeparatedFor.ext fun W k hk => ?_), ?_⟩
  · show (G.right.obj.map k.op).hom ((G.right.obj.map (ι U).op).hom s) =
      (G.right.obj.map k.op).hom ((G.right.obj.map (ι U).op).hom t)
    rw [AlgebraSheaf.map_map_apply, AlgebraSheaf.map_map_apply]
    exact h (k ≫ ι U) hk
  · intro U x hx
    let y : Presieve.FamilyOfElements (G.right.obj ⋙ forget CommRingCat.{u})
        (fun W (k : W ⟶ U' U) => R U (k ≫ ι U)) := fun W k hk => x (k ≫ ι U) hk
    have hy : y.Compatible := fun _ _ _ g₁ g₂ f₁ f₂ h₁ h₂ hcomm =>
      hx g₁ g₂ (f₁ ≫ ι U) (f₂ ≫ ι U) h₁ h₂ (by rw [← Category.assoc, hcomm, Category.assoc])
    obtain ⟨s, hs⟩ := (hbij U).2 ((hsh U).amalgamate y hy)
    refine ⟨s, fun W f hf => ?_⟩
    obtain ⟨k, rfl⟩ := hfac U W f hf
    rw [← AlgebraSheaf.map_map_apply, hs]
    exact (hsh U).valid_glue hy k hf

variable {V : Subfunctor Y.1} (hV : IsOpenImmersion B S hS V.ι)

/-- The affine charts over `U ×_Y V` which factor through `V` generate a covering sieve of it. -/
theorem generate_affineChartsOver_mem (U : SmallEtale B S hS Y.1) :
    Sieve.generate (fun W (k : W ⟶ openPreimageChart hV U) =>
        AlgebraSheaf.affineChartsOver V U (k ≫ openPreimageChartι hV U)) ∈
      SmallEtale.topology B S hS Y.1 (openPreimageChart hV U) := by
  refine GrothendieckTopology.superset_covering _ ?_
    (SmallEtale.ofArrows_openChart_affineOpens_mem B S hS Y.1 (openPreimageChart hV U))
  intro W k hk
  obtain ⟨Z, g, h, ⟨O⟩, rfl⟩ := hk
  exact ⟨_, g, openChartInclusion B S hS _ (openPreimageChart hV U) O.down.1, ⟨O.down.2,
    (range_le_range_of_hom (openChartInclusion B S hS _ (openPreimageChart hV U) O.down.1)).trans
      (range_openPreimageChart_le hV U)⟩, rfl⟩

variable {P : Over Y} (hP : yoneda.relativelyRepresentable P.hom.hom) (t : P.left.1 ⟶ V.toFunctor)
    (ht : t ≫ V.ι = P.hom.hom)

include hV hP ht in
/-- **The direct image of a space lying over `V` is separated, and glues, along the affine étale
charts factoring through `V`.** -/
theorem isSeparatedOn_and_gluesOn_pushforwardAlgebra :
    (pushforwardAlgebra B S hS P).IsSeparatedOn (AlgebraSheaf.affineChartsOver V) ∧
      (pushforwardAlgebra B S hS P).GluesOn (AlgebraSheaf.affineChartsOver V) :=
  isSeparatedOn_and_gluesOn_of_factor _ _ (openPreimageChart hV) (openPreimageChartι hV)
    (bijective_pushforwardAlgebra_map_openPreimageChartι hV hP t ht)
    (fun _ _ f hf => exists_comp_openPreimageChartι hV f hf.2)
    (generate_affineChartsOver_mem hV)

include hV hP ht in
/-- **A morphism of algebra sheaves which is an isomorphism over `V` induces a bijection on the
morphisms into the direct image of any space lying over `V`.** -/
theorem bijective_comp_pushforwardAlgebra_of_isIsoOver {A₁ A₂ : AlgebraSheaf.{u, u} B S hS Y.1 Y.2}
    {a : A₁ ⟶ A₂} (ha : AlgebraSheaf.IsIsoOver V a) :
    Function.Bijective (fun φ : A₂ ⟶ pushforwardAlgebra B S hS P => a ≫ φ) :=
  AlgebraSheaf.bijective_comp_of_isIsoOver ha
    (isSeparatedOn_and_gluesOn_pushforwardAlgebra hV hP t ht).1
    (isSeparatedOn_and_gluesOn_pushforwardAlgebra hV hP t ht).2

end Glueing

end AlgebraicGeometry.Space

end
