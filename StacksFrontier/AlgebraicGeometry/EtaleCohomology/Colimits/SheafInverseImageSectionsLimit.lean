module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.SmallEtaleSheafBaseChange
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Colimits.InverseImageSectionsLimit
import Mathlib.CategoryTheory.Adjunction.Restrict

/-!
# Sections of the inverse image of a sheaf of sets over a limit of schemes

Let `f : X ⟶ Y` be a morphism of schemes and `F` a sheaf of sets on the small étale site of `Y`.
The inverse image `f⁻¹F` (`Stacks.EtaleCohomology.smallEtaleSheafPullback`, the left adjoint of
the direct image) is the sheafification of the presheaf sending `U` to the colimit of the `F(W)`
over the pairs `(W, U ⟶ W ×_Y X)`, so its sections are described by two local statements:

* every section of `f⁻¹F` over `U` is, on a covering of `U`, the restriction of the image of a
  section of `F` over some `W` under the unit `F(W) ⟶ (f⁻¹F)(W ×_Y X)`;
* if two sections of `F` over `W` have the same image, restricted along `U ⟶ W ×_Y X`, then
  locally on `U` this restriction factors through some `W' ⟶ W` on which they agree.

For the limit `X = lim X_i` of a cofiltered system with affine transition morphisms, a sheaf of
sets `H` on a stage `X_i` and a quasi-compact object `V₀` of its small étale site, this gives
the injectivity half of `(f_i⁻¹H)(V₀ ×_{X_i} X) = colim_j (f_{ji}⁻¹H)(V₀ ×_{X_i} X_j)`
([Stacks, Tag 09YN] in degree zero): two sections of `H` over `V₀` with the same image over the
limit have the same image at some stage.

## Main definitions

* `Stacks.EtaleCohomology.smallEtaleSheafPullbackUnitApp`: the unit `F(W) ⟶ (f⁻¹F)(W ×_Y X)`.
* `Stacks.EtaleCohomology.smallEtaleSheafPullbackSectionsMap`: the comparison of sections of
  iterated inverse images `(f⁻¹H)(U) ⟶ ((gf)⁻¹H)(U ×_Y X)`.

## Main results

* `Stacks.EtaleCohomology.exists_covering_smallEtaleSheafPullback_eq_unitApp`: sections of `f⁻¹F`
  are locally images of sections of `F`.
* `Stacks.EtaleCohomology.exists_smallEtaleSheafPullbackUnitApp_eq_of_isLimit`: the injectivity
  half of the degree zero colimit formula.

## Implementation notes

The statements are those of
`Stacks.EtaleCohomology.exists_covering_smallEtalePullbackAb_eq_unitApp` and
`Stacks.EtaleCohomology.exists_unitApp_eq_zero_of_isLimit` for abelian sheaves, with the vanishing
of one section replaced by the agreement of two, which is what sheaves of sets need.
The agreement locus and the gluing of sections are those of
`Stacks.EtaleCohomology.smallEtaleEqLocus` and `Stacks.EtaleCohomology.exists_glue_smallEtale`,
which hold for any concrete coefficients.

## References

* [Stacks Project, Tag 09YN](https://stacks.math.columbia.edu/tag/09YN)
* [Stacks Project, Tag 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe u

namespace Stacks.EtaleCohomology

/-- The direct image of sheaves of sets along a morphism of schemes has a left adjoint. Stated
for every morphism at once, so that the inverse images of the systems of sheaves of sets and of
`Stacks.EtaleCohomology.smallEtaleSheafPullback` are taken with the same instance. -/
instance (priority := high) smallEtalePushforward_isRightAdjoint_type {X Y : Scheme.{u}}
    (f : X ⟶ Y) : (smallEtalePushforward f (Type (u + 1))).IsRightAdjoint := inferInstance

section Unit

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- The unit of the inverse image adjunction, on sections: `F(W) ⟶ (f⁻¹F)(W ×_Y X)`. -/
abbrev smallEtaleSheafPullbackUnitApp (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (W : Y.Etale) :
    F.obj.obj (op W) ⟶
      ((smallEtaleSheafPullback (Type (u + 1)) f).obj F).obj.obj
        (op ((smallEtaleBaseChange f).obj W)) :=
  ((smallEtaleSheafAdjunction (Type (u + 1)) f).unit.app F).hom.app (op W)

/-- The unit of the inverse image is natural in the object. -/
lemma smallEtaleSheafPullbackUnitApp_naturality (H : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    {U V : Y.Etale} (k : U ⟶ V) (h : H.obj.obj (op V)) :
    smallEtaleSheafPullbackUnitApp f H U (H.obj.map k.op h) =
      ((smallEtaleSheafPullback (Type (u + 1)) f).obj H).obj.map ((smallEtaleBaseChange f).map k).op
        (smallEtaleSheafPullbackUnitApp f H V h) :=
  congrArg (fun φ => φ h)
    (((smallEtaleSheafAdjunction (Type (u + 1)) f).unit.app H).hom.naturality k.op)

/-- The unit of the inverse image is natural in the sheaf. -/
lemma smallEtaleSheafPullbackUnitApp_map {F G : Sheaf (smallEtaleTopology Y) (Type (u + 1))}
    (φ : F ⟶ G) (U : Y.Etale) (h : F.obj.obj (op U)) :
    smallEtaleSheafPullbackUnitApp f G U (φ.hom.app (op U) h) =
      ((smallEtaleSheafPullback (Type (u + 1)) f).map φ).hom.app _
        (smallEtaleSheafPullbackUnitApp f F U h) := by
  have := congrArg (fun ψ => ψ.hom.app (op U) h)
    ((smallEtaleSheafAdjunction (Type (u + 1)) f).unit.naturality φ)
  simp only [Functor.id_obj, Functor.comp_obj, Functor.id_map, Functor.comp_map,
    ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app, ConcreteCategory.comp_apply] at this
  exact this

end Unit

/-! ### The local description of sections of an inverse image -/

section Construction

variable {X Y : Scheme.{u}} (f : X ⟶ Y)

/-- **A section of the left Kan extension is a pullback of a section of `F`.** -/
theorem exists_rep_smallEtaleSheafLan (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (U : X.Etale)
    (t : ((smallEtaleBaseChange f).op.lan.obj F.obj).obj (op U)) :
    ∃ (W : Y.Etale) (k : U ⟶ (smallEtaleBaseChange f).obj W) (s : F.obj.obj (op W)),
      ((smallEtaleBaseChange f).op.lan.obj F.obj).map k.op
        (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) s) = t := by
  have hcolim := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
      ((smallEtaleBaseChange f).op.lan.obj F.obj)
      ((smallEtaleBaseChange f).op.lanUnit.app F.obj) (op U)
  obtain ⟨j, y, hy⟩ := Types.jointly_surjective _ hcolim t
  exact ⟨j.left.unop, j.hom.unop, y, hy⟩

/-- **Agreement in the left Kan extension is witnessed over a single object.** -/
theorem exists_eq_of_smallEtaleSheafLan_eq (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    {U : X.Etale} {W : Y.Etale} (k : U ⟶ (smallEtaleBaseChange f).obj W)
    (h₁ h₂ : F.obj.obj (op W))
    (hz : ((smallEtaleBaseChange f).op.lan.obj F.obj).map k.op
      (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) h₁) =
        ((smallEtaleBaseChange f).op.lan.obj F.obj).map k.op
          (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) h₂)) :
    ∃ (W' : Y.Etale) (q : W' ⟶ W) (k' : U ⟶ (smallEtaleBaseChange f).obj W'),
      k' ≫ (smallEtaleBaseChange f).map q = k ∧ F.obj.map q.op h₁ = F.obj.map q.op h₂ := by
  have hcolim := Functor.isPointwiseLeftKanExtensionOfIsLeftKanExtension
      ((smallEtaleBaseChange f).op.lan.obj F.obj)
      ((smallEtaleBaseChange f).op.lanUnit.app F.obj) (op U)
  let j : CostructuredArrow (smallEtaleBaseChange f).op (op U) := CostructuredArrow.mk k.op
  obtain ⟨j', φ, φ₂, hφ⟩ := (Types.FilteredColimit.isColimit_eq_iff _ hcolim
    (i := j) (j := j) (xi := h₁) (xj := h₂)).mp hz
  let ψ := φ ≫ IsFiltered.coeqHom φ φ₂
  refine ⟨(IsFiltered.coeq φ φ₂).left.unop, ψ.left.unop, (IsFiltered.coeq φ φ₂).hom.unop,
    Quiver.Hom.op_inj (CostructuredArrow.w ψ), ?_⟩
  calc F.obj.map ψ.left h₁ = F.obj.map (IsFiltered.coeqHom φ φ₂).left (F.obj.map φ.left h₁) :=
        Functor.map_comp_apply F.obj φ.left (IsFiltered.coeqHom φ φ₂).left h₁
    _ = F.obj.map (IsFiltered.coeqHom φ φ₂).left (F.obj.map φ₂.left h₂) := congrArg _ hφ
    _ = F.obj.map (φ₂ ≫ IsFiltered.coeqHom φ φ₂).left h₂ :=
        (Functor.map_comp_apply F.obj φ₂.left (IsFiltered.coeqHom φ φ₂).left h₂).symm
    _ = F.obj.map ψ.left h₂ := by rw [← IsFiltered.coeq_condition]

/-- The unit of Mathlib's construction of the inverse image, on underlying presheaves: the unit
of the left Kan extension followed by sheafification. -/
lemma smallEtaleSheafAdjunctionConstruction_unit_app_hom
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) :
    ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange f)
        (Type (u + 1)) (smallEtaleTopology Y) (smallEtaleTopology X)).unit.app F).hom =
      (smallEtaleBaseChange f).op.lanUnit.app F.obj ≫
        Functor.whiskerLeft (smallEtaleBaseChange f).op
          (toSheafify (smallEtaleTopology X) ((smallEtaleBaseChange f).op.lan.obj F.obj)) := by
  refine (Adjunction.map_restrictFullyFaithful_unit_app
    (adj := ((smallEtaleBaseChange f).op.lanAdjunction (Type (u + 1))).comp
      (sheafificationAdjunction (smallEtaleTopology X) (Type (u + 1))))
    (hiC := fullyFaithfulSheafToPresheaf (smallEtaleTopology Y) (Type (u + 1)))
    (hiD := Functor.FullyFaithful.id _)
    (L := Functor.sheafPullbackConstruction.sheafPullback (smallEtaleBaseChange f) (Type (u + 1))
      (smallEtaleTopology Y) (smallEtaleTopology X))
    (R := (smallEtaleBaseChange f).sheafPushforwardContinuous (Type (u + 1))
      (smallEtaleTopology Y) (smallEtaleTopology X))
    (comm1 := Iso.refl _) (comm2 := Iso.refl _) F).trans ?_
  ext
  rfl

/-- The comparison of the inverse image with Mathlib's construction carries the unit to the unit
of the construction. -/
lemma smallEtaleSheafPullbackConstructionIso_unitApp
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    (W : Y.Etale) (h : F.obj.obj (op W)) :
    ((Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange f) (Type (u + 1))
        (smallEtaleTopology Y) (smallEtaleTopology X)).hom.app F).hom.app
        (op ((smallEtaleBaseChange f).obj W)) (smallEtaleSheafPullbackUnitApp f F W h) =
      (toSheafify (smallEtaleTopology X) ((smallEtaleBaseChange f).op.lan.obj F.obj)).app
        (op ((smallEtaleBaseChange f).obj W))
        (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) h) := by
  have hu := congrArg (fun φ => (φ.hom.app (op W)) h)
    (Adjunction.unit_leftAdjointUniq_hom_app (smallEtaleSheafAdjunction (Type (u + 1)) f)
      (Functor.sheafPullbackConstruction.sheafAdjunctionContinuous (smallEtaleBaseChange f)
        (Type (u + 1)) (smallEtaleTopology Y) (smallEtaleTopology X)) F)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply, smallEtaleSheafAdjunctionConstruction_unit_app_hom f F,
    Functor.whiskerLeft_app] at hu
  exact hu

/-- The sheafification of a restricted image of a section under the unit of the left Kan
extension is the restricted image of the section under the unit of the inverse image. -/
private lemma toSheafify_map_lanUnit_eq (F : Sheaf (smallEtaleTopology Y) (Type (u + 1)))
    {U : X.Etale} {W : Y.Etale} (m : U ⟶ (smallEtaleBaseChange f).obj W) (h : F.obj.obj (op W)) :
    (toSheafify (smallEtaleTopology X) ((smallEtaleBaseChange f).op.lan.obj F.obj)).app (op U)
        (((smallEtaleBaseChange f).op.lan.obj F.obj).map m.op
          (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) h)) =
      ((Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange f)
        (Type (u + 1)) (smallEtaleTopology Y) (smallEtaleTopology X)).hom.app F).hom.app (op U)
        (((smallEtaleSheafPullback (Type (u + 1)) f).obj F).obj.map m.op
          (smallEtaleSheafPullbackUnitApp f F W h)) := by
  let ε := Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange f)
    (Type (u + 1)) (smallEtaleTopology Y) (smallEtaleTopology X)
  have nat₂ := congrArg (fun φ => φ (smallEtaleSheafPullbackUnitApp f F W h))
    ((ε.hom.app F).hom.naturality m.op)
  have nat₃ := congrArg
    (fun φ => φ (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) h))
    ((toSheafify (smallEtaleTopology X) ((smallEtaleBaseChange f).op.lan.obj F.obj)).naturality
      m.op)
  simp only [ConcreteCategory.comp_apply] at nat₂ nat₃
  rw [smallEtaleSheafPullbackConstructionIso_unitApp] at nat₂
  exact nat₃.trans nat₂.symm

/-- **Sections of an inverse image are locally images of sections of the sheaf.** -/
theorem exists_covering_smallEtaleSheafPullback_eq_unitApp
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) (U : X.Etale)
    (x : ((smallEtaleSheafPullback (Type (u + 1)) f).obj F).obj.obj (op U)) :
    ∃ S ∈ smallEtaleTopology X U, ∀ ⦃U' : X.Etale⦄ (g : U' ⟶ U), S g →
      ∃ (W : Y.Etale) (m : U' ⟶ (smallEtaleBaseChange f).obj W)
        (h : F.obj.obj (op W)),
        ((smallEtaleSheafPullback (Type (u + 1)) f).obj F).obj.map g.op x =
          ((smallEtaleSheafPullback (Type (u + 1)) f).obj F).obj.map m.op
            (smallEtaleSheafPullbackUnitApp f F W h) := by
  let ε := Functor.sheafPullbackConstruction.sheafPullbackIso (smallEtaleBaseChange f)
    (Type (u + 1)) (smallEtaleTopology Y) (smallEtaleTopology X)
  let P := (smallEtaleBaseChange f).op.lan.obj F.obj
  set x' := (ε.hom.app F).hom.app (op U) x
  refine ⟨Presheaf.imageSieve (toSheafify (smallEtaleTopology X) P) x',
    (Presheaf.isLocallySurjective_toSheafify' _ P).imageSieve_mem x', ?_⟩
  rintro U' g ⟨y, hy⟩
  obtain ⟨W, k, s, hks⟩ := exists_rep_smallEtaleSheafLan f F U' y
  refine ⟨W, k, s, ?_⟩
  apply ((isIso_iff_bijective ((ε.hom.app F).hom.app (op U'))).mp inferInstance).1
  have nat₁ := congrArg (fun φ => φ x) ((ε.hom.app F).hom.naturality g.op)
  simp only [ConcreteCategory.comp_apply] at nat₁
  refine nat₁.trans (hy.symm.trans ?_)
  rw [← hks]
  exact toSheafify_map_lanUnit_eq f F k s

/-- **Two sections with the same image in the inverse image agree locally further down.** If
two sections `h₁, h₂` of `F` over `W` have the same image, restricted along
`m : U ⟶ W ×_Y X`, then on a covering sieve of `U` every restriction `U' ⟶ U` of `m` factors
through `W' ×_Y X` for some `q : W' ⟶ W` with `h₁|_{W'} = h₂|_{W'}`. -/
theorem exists_covering_of_smallEtaleSheafPullback_unitApp_eq
    (F : Sheaf (smallEtaleTopology Y) (Type (u + 1))) {U : X.Etale} {W : Y.Etale}
    (m : U ⟶ (smallEtaleBaseChange f).obj W) (h₁ h₂ : F.obj.obj (op W))
    (hz : ((smallEtaleSheafPullback (Type (u + 1)) f).obj F).obj.map m.op
        (smallEtaleSheafPullbackUnitApp f F W h₁) =
      ((smallEtaleSheafPullback (Type (u + 1)) f).obj F).obj.map m.op
        (smallEtaleSheafPullbackUnitApp f F W h₂)) :
    ∃ S ∈ smallEtaleTopology X U, ∀ ⦃U' : X.Etale⦄ (g : U' ⟶ U), S g →
      ∃ (W' : Y.Etale) (q : W' ⟶ W) (m' : U' ⟶ (smallEtaleBaseChange f).obj W'),
        m' ≫ (smallEtaleBaseChange f).map q = g ≫ m ∧ F.obj.map q.op h₁ = F.obj.map q.op h₂ := by
  let P := (smallEtaleBaseChange f).op.lan.obj F.obj
  let y₁ := P.map m.op (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) h₁)
  let y₂ := P.map m.op (((smallEtaleBaseChange f).op.lanUnit.app F.obj).app (op W) h₂)
  have hy : (toSheafify (smallEtaleTopology X) P).app (op U) y₁ =
      (toSheafify (smallEtaleTopology X) P).app (op U) y₂ := by
    rw [toSheafify_map_lanUnit_eq f F m h₁, toSheafify_map_lanUnit_eq f F m h₂, hz]
  refine ⟨Presheaf.equalizerSieve (F := P) y₁ y₂,
    (Presheaf.isLocallyInjective_toSheafify' _ P).equalizerSieve_mem y₁ y₂ hy, fun U' g hg => ?_⟩
  refine exists_eq_of_smallEtaleSheafLan_eq f F (g ≫ m) h₁ h₂ ?_
  rwa [op_comp, Functor.map_comp_apply, Functor.map_comp_apply]

end Construction

/-! ### The injectivity half -/

section Limit

variable {I : Type u} [SmallCategory I] [IsCofiltered I] (D : I ⥤ Scheme.{u}) (c : Cone D)
  (hc : IsLimit c) [∀ {i j : I} (f : i ⟶ j), IsAffineHom (D.map f)]

include hc in
/-- **The injectivity half of the degree zero colimit formula for an inverse image.** Let
`X = lim X_i` be a cofiltered limit with affine transition morphisms, `H` a sheaf on the small
étale site of a stage `X_i` and `h₁, h₂` two sections of `H` over a quasi-compact object `V₀`. If
their images in the sections of `f_i⁻¹H` over the base change of `V₀` to `X` agree, then their
images in the sections of the inverse image of `H` over the base change of `V₀` to some later
stage `X_j` already agree. -/
theorem exists_smallEtaleSheafPullbackUnitApp_eq_of_isLimit {i : I}
    (H : Sheaf (smallEtaleTopology (D.obj i)) (Type (u + 1))) (V₀ : (D.obj i).Etale)
    [CompactSpace V₀.left]
    (h₁ h₂ : H.obj.obj (op V₀))
    (hz : smallEtaleSheafPullbackUnitApp (c.π.app i) H V₀ h₁ =
      smallEtaleSheafPullbackUnitApp (c.π.app i) H V₀ h₂) :
    ∃ (j : I) (f : j ⟶ i), smallEtaleSheafPullbackUnitApp (D.map f) H V₀ h₁ =
      smallEtaleSheafPullbackUnitApp (D.map f) H V₀ h₂ := by
  let O := smallEtaleEqLocus H V₀ h₁ h₂
  obtain ⟨S, hS, hSz⟩ := exists_covering_of_smallEtaleSheafPullback_unitApp_eq (c.π.app i) H
    (𝟙 _) h₁ h₂ (by
      simpa only [op_id, CategoryTheory.Functor.map_id, ConcreteCategory.id_apply] using hz)
  have hlim : Set.range (pullback.snd (c.π.app i) V₀.hom) ⊆ (O : Set V₀.left) := by
    rw [Scheme.Pullback.range_snd, ← Scheme.Pullback.range_fst]
    rintro _ ⟨x, rfl⟩
    obtain ⟨U', g, hg, u, rfl⟩ := exists_mem_range_of_mem_smallEtaleTopology S hS x
    obtain ⟨W', q, m', hm', hq⟩ := hSz g hg
    have hsub := range_subset_smallEtaleEqLocus H q h₁ h₂
    refine hsub hq ⟨(m'.left ≫ pullback.fst W'.hom _) u, ?_⟩
    have e := congrArg (fun φ => φ.left ≫ pullback.fst V₀.hom (c.π.app i))
      (hm'.trans (Category.comp_id g))
    have e2 : (m'.left ≫ pullback.fst W'.hom (c.π.app i)) ≫ q.left =
        g.left ≫ pullback.fst V₀.hom (c.π.app i) :=
      (Category.assoc _ _ _).trans ((congrArg (fun ψ => m'.left ≫ ψ)
        (smallEtaleBaseChange_map_left_fst (c.π.app i) q).symm).trans
          ((Category.assoc _ _ _).symm.trans e))
    exact congrArg (fun φ => φ u) e2
  obtain ⟨j, f, hj⟩ := exists_range_pullback_snd_subset_of_isLimit D c hc
    (Z := V₀.left) V₀.hom O hlim
  refine ⟨j, f, ?_⟩
  rw [Scheme.Pullback.range_snd, ← Scheme.Pullback.range_fst] at hj
  let T := (smallEtaleBaseChange (D.map f)).obj V₀
  let S' : Sieve T := Sieve.generate fun U' g =>
    ∃ (U : (D.obj i).Etale) (k : U ⟶ V₀), H.obj.map k.op h₁ = H.obj.map k.op h₂ ∧
      ∃ g' : U' ⟶ (smallEtaleBaseChange (D.map f)).obj U,
        g = g' ≫ (smallEtaleBaseChange (D.map f)).map k
  have hS' : S' ∈ smallEtaleTopology (D.obj j) T := by
    obtain ⟨α, Y, p, hEq⟩ := S'.exists_eq_ofArrows
    rw [hEq, Scheme.ofArrows_mem_smallEtaleTopology_iff]
    refine Set.eq_univ_of_forall fun y => ?_
    have hmemO := fun x hx => exists_of_mem_smallEtaleEqLocus (x := x) H h₁ h₂ hx
    obtain ⟨U, k, hk, u, hu⟩ := hmemO _ (hj ⟨y, rfl⟩)
    obtain ⟨w, rfl⟩ : y ∈ Set.range ((smallEtaleBaseChange (D.map f)).map k).left := by
      rw [range_smallEtaleBaseChange_map]
      exact ⟨u, hu⟩
    have hmem : (Sieve.ofArrows Y p).arrows ((smallEtaleBaseChange (D.map f)).map k) := by
      rw [← hEq]
      exact Sieve.le_generate _ _ _ ⟨U, k, hk, 𝟙 _, (Category.id_comp _).symm⟩
    obtain ⟨a, e, he⟩ := (Sieve.mem_ofArrows_iff _ _ _).mp hmem
    exact Set.mem_iUnion.2 ⟨a, e.left w, (congrArg (fun φ => φ.left w) he).symm⟩
  refine smallEtale_section_ext ((smallEtaleSheafPullback (Type (u + 1)) (D.map f)).obj H) S' hS'
    _ _ fun U' g hg => ?_
  obtain ⟨U'', g₁, g₂, ⟨U, k, hk, g', rfl⟩, rfl⟩ := hg
  change ((smallEtaleSheafPullback (Type (u + 1)) (D.map f)).obj H).obj.map (g₁ ≫ g' ≫ _).op
      (smallEtaleSheafPullbackUnitApp (D.map f) H V₀ h₁) =
    ((smallEtaleSheafPullback (Type (u + 1)) (D.map f)).obj H).obj.map (g₁ ≫ g' ≫ _).op
      (smallEtaleSheafPullbackUnitApp (D.map f) H V₀ h₂)
  rw [op_comp, op_comp, Functor.map_comp_apply, Functor.map_comp_apply,
    Functor.map_comp_apply, Functor.map_comp_apply,
    ← smallEtaleSheafPullbackUnitApp_naturality, ← smallEtaleSheafPullbackUnitApp_naturality,
    hk]

end Limit

/-! ### Comparison of sections of iterated inverse images -/

section PullbackSectionsMap

variable {X Y Z : Scheme.{u}} (g : X ⟶ Y) (f : Y ⟶ Z) (gf : X ⟶ Z) (hgf : gf = g ≫ f)

/-- Sections of `f⁻¹H` over `U` map to sections of `(gf)⁻¹H` over `U ×_Y X`: the unit of
`g⁻¹ ⊣ g_*` followed by the comparison `g⁻¹f⁻¹ ≅ (gf)⁻¹`. -/
def smallEtaleSheafPullbackSectionsMap (H : Sheaf (smallEtaleTopology Z) (Type (u + 1)))
    (U : Y.Etale) :
    ((smallEtaleSheafPullback (Type (u + 1)) f).obj H).obj.obj (op U) ⟶
      ((smallEtaleSheafPullback (Type (u + 1)) gf).obj H).obj.obj
        (op ((smallEtaleBaseChange g).obj U)) :=
  smallEtaleSheafPullbackUnitApp g ((smallEtaleSheafPullback (Type (u + 1)) f).obj H) U ≫
    ((smallEtaleSheafPullbackCompApp (Type (u + 1)) g f gf hgf H).hom).hom.app
      (op ((smallEtaleBaseChange g).obj U))

/-- The comparison of sections is natural in the object. -/
lemma smallEtaleSheafPullbackSectionsMap_naturality
    (H : Sheaf (smallEtaleTopology Z) (Type (u + 1)))
    {U U' : Y.Etale} (k : U' ⟶ U)
    (x : ((smallEtaleSheafPullback (Type (u + 1)) f).obj H).obj.obj (op U)) :
    smallEtaleSheafPullbackSectionsMap g f gf hgf H U'
        (((smallEtaleSheafPullback (Type (u + 1)) f).obj H).obj.map k.op x) =
      ((smallEtaleSheafPullback (Type (u + 1)) gf).obj H).obj.map
          ((smallEtaleBaseChange g).map k).op
        (smallEtaleSheafPullbackSectionsMap g f gf hgf H U x) := by
  dsimp only [smallEtaleSheafPullbackSectionsMap]
  rw [ConcreteCategory.comp_apply, ConcreteCategory.comp_apply,
    smallEtaleSheafPullbackUnitApp_naturality]
  exact congrArg (fun φ => φ (smallEtaleSheafPullbackUnitApp g _ U x))
    (((smallEtaleSheafPullbackCompApp (Type (u + 1)) g f gf hgf H).hom).hom.naturality
      ((smallEtaleBaseChange g).map k).op)

/-- **The unit of a composite adjunction, on sections.** The comparison of sections carries the
image of a section of `H` under the unit of `f⁻¹ ⊣ f_*` to its image under the unit of
`(gf)⁻¹ ⊣ (gf)_*`, read through the identification of the iterated base change. -/
lemma smallEtaleSheafPullbackSectionsMap_unitApp (H : Sheaf (smallEtaleTopology Z) (Type (u + 1)))
    (V₀ : Z.Etale) (h : H.obj.obj (op V₀)) :
    ((smallEtaleSheafPullback (Type (u + 1)) gf).obj H).obj.map
        ((smallEtaleBaseChangeComp' g f gf hgf).hom.app V₀).op
        (smallEtaleSheafPullbackSectionsMap g f gf hgf H ((smallEtaleBaseChange f).obj V₀)
          (smallEtaleSheafPullbackUnitApp f H V₀ h)) =
      smallEtaleSheafPullbackUnitApp gf H V₀ h := by
  have hu := congrArg (fun φ => φ.hom.app (op V₀) h)
    (smallEtaleSheafAdjunction_unit_app_comp (Type (u + 1)) g f gf hgf H)
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at hu
  refine Eq.trans ?_ hu.symm
  have he := smallEtalePushforwardComp'_hom_app_hom_app g f gf hgf (Type (u + 1))
    ((smallEtaleSheafPullback (Type (u + 1)) g).obj
      ((smallEtaleSheafPullback (Type (u + 1)) f).obj H)) (op V₀)
  have hn := congrArg (fun φ => φ (smallEtaleSheafPullbackUnitApp g
      ((smallEtaleSheafPullback (Type (u + 1)) f).obj H) ((smallEtaleBaseChange f).obj V₀)
      (smallEtaleSheafPullbackUnitApp f H V₀ h)))
    (((smallEtaleSheafPullbackCompApp (Type (u + 1)) g f gf hgf H).hom).hom.naturality
      ((smallEtaleBaseChangeComp' g f gf hgf).hom.app V₀).op)
  simp only [ConcreteCategory.comp_apply] at hn
  exact hn.symm.trans <|
    congrArg
      (fun z => ((smallEtaleSheafPullbackCompApp (Type (u + 1)) g f gf hgf H).hom).hom.app _ z)
      (congrArg (fun φ => φ (smallEtaleSheafPullbackUnitApp g
        ((smallEtaleSheafPullback (Type (u + 1)) f).obj H) ((smallEtaleBaseChange f).obj V₀)
        (smallEtaleSheafPullbackUnitApp f H V₀ h))) he.symm)

end PullbackSectionsMap

end Stacks.EtaleCohomology

end
