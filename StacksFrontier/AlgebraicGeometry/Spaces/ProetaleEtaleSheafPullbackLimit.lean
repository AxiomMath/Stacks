module

public import Mathlib.AlgebraicGeometry.AffineTransitionLimit
public import StacksFrontier.AlgebraicGeometry.Spaces.ProetaleEtaleSheafPullbackUnit

/-!
# Sections of the pro-étale inverse image of an étale sheaf at a limit of pro-étale objects

Let `X` be a scheme and let `ε : X_proétale → X_étale` be the morphism of sites given by the
inclusion of the small étale category into the small pro-étale category.  Let `Y = lim Y_i` be the
limit of an inverse system of quasi-compact objects of `X_proétale` with affine transition
morphisms.  For a sheaf `ℱ` on `X_étale`, two sections of `ε⁻¹ℱ` over a stage `Y_i` which have the
same restriction to `Y` already have the same restriction to some later stage `Y_j`.

This is the injectivity half of the formula `ε⁻¹ℱ(Y) = colim ε⁻¹ℱ(Y_i)` of Stacks 099S: it says
that the canonical map `colim ε⁻¹ℱ(Y_i) → ε⁻¹ℱ(Y)` out of the filtered colimit is injective.  The
surjectivity half, that every section over `Y` comes from a stage, is not proved here.

## Main results

* `AlgebraicGeometry.Scheme.etaleSectionsSheaf_exists_map_eq_of_isLimit`: the statement for the
  rule `(f : Y → X) ↦ Γ(Y_étale, f_étale⁻¹ℱ)` of Stacks 0GLZ.
* `AlgebraicGeometry.Scheme.proetaleInverseImage_exists_map_eq_of_isLimit`: the same for `ε⁻¹ℱ`,
  the inverse image of `ℱ` along `ε`.
* `AlgebraicGeometry.Scheme.injective_desc_proetaleInverseImage_of_isLimit`: the comparison map
  `colim ε⁻¹ℱ(Y_i) → ε⁻¹ℱ(Y)` is injective.
* `AlgebraicGeometry.Scheme.etaleSections_exists_map_eq_of_isLimit`: the final statement of the
  tag, `ε⁻¹ℱ(Y) = colim ℱ(Y_i)` for étale stages, in the same half.

## Implementation notes

By Stacks 0GLZ the sections of `ε⁻¹ℱ` at a pro-étale object are the sections, over the underlying
`X`-scheme, of the inverse image of `ℱ` on all `X`-schemes, and
`AlgebraicGeometry.Scheme.bigEtaleInverseImage_openEq_over` exhibits the locus where two such
sections agree as an open `W` of `Y_i`.  The hypothesis then says that `Y → Y_i` lands in `W` and
the conclusion that some transition morphism `Y_j → Y_i` does; that passage is Stacks 01Z4,
`AlgebraicGeometry.exists_map_preimage_le_map_preimage`, applied to the open `⊤` of the stage.
Quasi-compactness of the stages is what makes `⊤` compact; quasi-separatedness is not used.

That the limit is taken in the pro-étale site is not what the argument needs, and the source
takes it in schemes: the hypothesis here is that the cone of underlying `X`-schemes is a limit
cone.  The index category is a small category in the universe of the schemes, which is the
generality of the limit API used, and the coefficient universe stays free.

## References

* [Stacks Project, Tag 099S](https://stacks.math.columbia.edu/tag/099S)
* [Stacks Project, Tag 0GLZ](https://stacks.math.columbia.edu/tag/0GLZ)
* [Stacks Project, Tag 01Z4](https://stacks.math.columbia.edu/tag/01Z4)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry Opposite

universe u v

namespace AlgebraicGeometry

/-- Restrictions of two sections agree after applying an isomorphism of presheaves of types
if and only if they agree before. -/
private theorem map_hom_app_eq_iff_of_iso {C : Type*} [Category C] {P Q : Cᵒᵖ ⥤ Type v}
    (e : P ≅ Q) {a b : Cᵒᵖ} (f : a ⟶ b) (s t : P.obj a) :
    Q.map f (e.hom.app a s) = Q.map f (e.hom.app a t) ↔ P.map f s = P.map f t := by
  rw [← NatTrans.naturality_apply, ← NatTrans.naturality_apply]
  exact (ConcreteCategory.bijective_of_isIso (e.hom.app b)).injective.eq_iff

/-- **Stacks 099S for the formula of Stacks 0GLZ, the injectivity half.** Two sections of the
rule `(f : Y → X) ↦ Γ(Y_étale, f_étale⁻¹ℱ)` over a stage `Y_i` of an inverse system of
quasi-compact pro-étale objects with affine transitions whose underlying schemes have limit `Y`,
and which agree over `Y`, already agree over some later stage. -/
public theorem Scheme.etaleSectionsSheaf_exists_map_eq_of_isLimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] (X : Scheme.{u}) (Y : I ⥤ X.ProEt)
    (c : Cone Y) (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    (haffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (Y.map f).left)
    (hqc : ∀ i : I, CompactSpace (Y.obj i).left)
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v))) (i : I)
    (s t : ((Scheme.etaleSectionsSheaf.{u, v} X).obj F).obj.obj (op (Y.obj i)))
    (hst : ((Scheme.etaleSectionsSheaf.{u, v} X).obj F).obj.map (c.π.app i).op s =
      ((Scheme.etaleSectionsSheaf.{u, v} X).obj F).obj.map (c.π.app i).op t) :
    ∃ (j : I) (f : j ⟶ i),
      ((Scheme.etaleSectionsSheaf.{u, v} X).obj F).obj.map (Y.map f).op s =
        ((Scheme.etaleSectionsSheaf.{u, v} X).obj F).obj.map (Y.map f).op t := by
  let D : I ⥤ Scheme.{u} := Y ⋙ Scheme.ProEt.forget X ⋙ Over.forget X
  have : ∀ {a b : I} (f : a ⟶ b), IsAffineHom (D.map f) := fun f => haffine f
  have : ∀ a : I, CompactSpace (D.obj a) := hqc
  obtain ⟨W, hW⟩ := Scheme.bigEtaleInverseImage_openEq_over.{u, v} X F
    ((Scheme.ProEt.forget X).obj (Y.obj i)) s t
  obtain ⟨j, f, hjf⟩ := exists_map_preimage_le_map_preimage D
    ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c) hc (U := ⊤) (V := W)
    (by simpa using isCompact_univ)
    (by
      rw [← SetLike.coe_subset_coe]
      rintro x -
      exact (hW _ ((Scheme.ProEt.forget X).map (c.π.app i))).mp hst (Set.mem_range_self x))
  refine ⟨j, f, (hW _ ((Scheme.ProEt.forget X).map (Y.map f))).mpr ?_⟩
  rintro _ ⟨x, rfl⟩
  exact hjf (show x ∈ D.map f ⁻¹ᵁ (⊤ : (D.obj i).Opens) from trivial)

/-- **Stacks 099S, the injectivity half.** Let `Y = lim Y_i` be the limit of an inverse system of
quasi-compact objects of `X_proétale` with affine transition morphisms, and let `ℱ` be a sheaf on
`X_étale`.  Two sections of `ε⁻¹ℱ` over a stage `Y_i` with the same restriction to `Y` already
have the same restriction to some later stage `Y_j`; equivalently, the canonical map
`colim ε⁻¹ℱ(Y_i) → ε⁻¹ℱ(Y)` is injective.

The sections are computed by the formula of Stacks 0GLZ through
`AlgebraicGeometry.Scheme.proetaleInverseImageIsoEtaleSectionsSheaf`, which turns this into
`AlgebraicGeometry.Scheme.etaleSectionsSheaf_exists_map_eq_of_isLimit`. -/
@[stacks 099S "the injectivity half of ε⁻¹ℱ(Y) = colim ε⁻¹ℱ(Y_i), proved: two sections over a \
stage that agree over the limit agree over a later stage.  The surjectivity half, hence the \
formula itself, is not proved here.  `Y = lim Y_i` is the scheme-theoretic limit, as in the \
source; the index category is small in the universe of the schemes"]
public theorem Scheme.proetaleInverseImage_exists_map_eq_of_isLimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] (X : Scheme.{u}) (Y : I ⥤ X.ProEt)
    (c : Cone Y) (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    (haffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (Y.map f).left)
    (hqc : ∀ i : I, CompactSpace (Y.obj i).left)
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v))) (i : I)
    (s t : ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology
      (Scheme.ProEt.topology X)).obj F).obj.obj (op (Y.obj i)))
    (hst : ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology
        (Scheme.ProEt.topology X)).obj F).obj.map (c.π.app i).op s =
      ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology
        (Scheme.ProEt.topology X)).obj F).obj.map (c.π.app i).op t) :
    ∃ (j : I) (f : j ⟶ i),
      ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
          (Type (max (u + 1) v)) X.smallEtaleTopology
          (Scheme.ProEt.topology X)).obj F).obj.map (Y.map f).op s =
        ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
          (Type (max (u + 1) v)) X.smallEtaleTopology
          (Scheme.ProEt.topology X)).obj F).obj.map (Y.map f).op t := by
  let e : ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj ≅
      ((Scheme.etaleSectionsSheaf.{u, v} X).obj F).obj :=
    (sheafToPresheaf (Scheme.ProEt.topology X) (Type (max (u + 1) v))).mapIso
      ((Scheme.proetaleInverseImageIsoEtaleSectionsSheaf.{u, v} X).app F)
  obtain ⟨j, f, hjf⟩ := Scheme.etaleSectionsSheaf_exists_map_eq_of_isLimit.{u, v} X Y c hc
    haffine hqc F i (e.hom.app _ s) (e.hom.app _ t)
    ((map_hom_app_eq_iff_of_iso e _ s t).2 hst)
  exact ⟨j, f, (map_hom_app_eq_iff_of_iso e _ s t).1 hjf⟩

/-- **Stacks 099S, the injectivity half, for the comparison map out of the colimit.** The
canonical map `colim ε⁻¹ℱ(Y_i) → ε⁻¹ℱ(Y)` induced by the limit cone is injective, for any cocone
exhibiting the colimit of the sections at the stages.

Elements of a filtered colimit come from a stage and the comparison map restricts on a stage to
restriction along the cone leg, so this is
`AlgebraicGeometry.Scheme.proetaleInverseImage_exists_map_eq_of_isLimit` at a stage below both. -/
@[stacks 099S "proved: the comparison map colim ε⁻¹ℱ(Y_i) → ε⁻¹ℱ(Y) of the displayed formula is \
INJECTIVE, for every colimit cocone of the sections at the stages.  Its surjectivity is not \
proved, so the formula itself is not"]
public theorem Scheme.injective_desc_proetaleInverseImage_of_isLimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] (X : Scheme.{u}) (Y : I ⥤ X.ProEt)
    (c : Cone Y) (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    (haffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (Y.map f).left)
    (hqc : ∀ i : I, CompactSpace (Y.obj i).left)
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v)))
    (E : Cocone (Y.op ⋙ ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
      (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj))
    (hE : IsColimit E) :
    Function.Injective (hE.desc (((Functor.sheafPullbackConstruction.sheafPullback
      X.etaleToProetale (Type (max (u + 1) v)) X.smallEtaleTopology
      (Scheme.ProEt.topology X)).obj F).obj.mapCocone c.op)) := by
  intro x y hxy
  let s := ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
    (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj.mapCocone
      c.op
  obtain ⟨i, a, ha⟩ := Types.jointly_surjective_of_isColimit hE x
  obtain ⟨j, b, hb⟩ := Types.jointly_surjective_of_isColimit hE y
  have key : ∀ (m : Iᵒᵖ) (z : _), hE.desc s (E.ι.app m z) = s.ι.app m z :=
    fun m z => ConcreteCategory.congr_hom (hE.fac s m) z
  have hw : ∀ {m m' : Iᵒᵖ} (g : m ⟶ m') (z : _),
      E.ι.app m' (((Y.op ⋙ _) : Iᵒᵖ ⥤ Type (max (u + 1) v)).map g z) = E.ι.app m z :=
    fun g z => ConcreteCategory.congr_hom (E.w g) z
  let k : I := IsCofiltered.min i.unop j.unop
  let fi : k ⟶ i.unop := IsCofiltered.minToLeft i.unop j.unop
  let fj : k ⟶ j.unop := IsCofiltered.minToRight i.unop j.unop
  have hxk := (hw fi.op a).trans ha
  have hyk := (hw fj.op b).trans hb
  have h : s.ι.app (op k) (((Y.op ⋙ _) : Iᵒᵖ ⥤ Type (max (u + 1) v)).map fi.op a) =
      s.ι.app (op k) (((Y.op ⋙ _) : Iᵒᵖ ⥤ Type (max (u + 1) v)).map fj.op b) := by
    rw [← key (op k), ← key (op k), hxk, hyk, hxy]
  obtain ⟨l, g, hlg⟩ := Scheme.proetaleInverseImage_exists_map_eq_of_isLimit.{u, v} X Y c hc
    haffine hqc F k _ _ h
  exact (hxk.symm.trans ((hw g.op _).symm.trans
    ((congrArg (E.ι.app (op l)) hlg).trans (hw g.op _)))).trans hyk

/-- **Stacks 099S for étale stages, the injectivity half.** If the stages `Y_i` are objects of
`X_étale`, two sections of `ℱ` over a stage whose images in `ε⁻¹ℱ(Y)` under the unit
`ℱ ⟶ ε_*ε⁻¹ℱ` agree already agree over some later stage; equivalently, the canonical map
`colim ℱ(Y_i) → ε⁻¹ℱ(Y)` is injective.

The unit is an isomorphism by Stacks 099T, naturally in the étale object, which reduces this to
`AlgebraicGeometry.Scheme.proetaleInverseImage_exists_map_eq_of_isLimit`. -/
@[stacks 099S "the final statement ε⁻¹ℱ(Y) = colim ℱ(Y_i) for étale stages, injectivity half \
proved: two sections of ℱ over a stage with the same image in ε⁻¹ℱ(Y) agree over a later stage.  \
Surjectivity is not proved, so the formula itself is not"]
public theorem Scheme.etaleSections_exists_map_eq_of_isLimit
    {I : Type u} [SmallCategory I] [IsCofiltered I] (X : Scheme.{u}) (Y : I ⥤ X.Etale)
    (c : Cone (Y ⋙ X.etaleToProetale))
    (hc : IsLimit ((Scheme.ProEt.forget X ⋙ Over.forget X).mapCone c))
    (haffine : ∀ {i j : I} (f : i ⟶ j), IsAffineHom (Y.map f).left)
    (hqc : ∀ i : I, CompactSpace (Y.obj i).left)
    (F : Sheaf X.smallEtaleTopology (Type (max (u + 1) v))) (i : I)
    (s t : F.obj.obj (op (Y.obj i)))
    (hst : ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
          (Type (max (u + 1) v)) X.smallEtaleTopology
          (Scheme.ProEt.topology X)).obj F).obj.map (c.π.app i).op
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
          (Type (max (u + 1) v)) X.smallEtaleTopology
          (Scheme.ProEt.topology X)).unit.app F).hom.app (op (Y.obj i)) s) =
      ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
          (Type (max (u + 1) v)) X.smallEtaleTopology
          (Scheme.ProEt.topology X)).obj F).obj.map (c.π.app i).op
        (((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
          (Type (max (u + 1) v)) X.smallEtaleTopology
          (Scheme.ProEt.topology X)).unit.app F).hom.app (op (Y.obj i)) t)) :
    ∃ (j : I) (f : j ⟶ i), F.obj.map (Y.map f).op s = F.obj.map (Y.map f).op t := by
  let e : F.obj ≅ X.etaleToProetale.op ⋙
      ((Functor.sheafPullbackConstruction.sheafPullback X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).obj F).obj :=
    (sheafToPresheaf X.smallEtaleTopology (Type (max (u + 1) v))).mapIso
      (asIso ((Functor.sheafPullbackConstruction.sheafAdjunctionContinuous X.etaleToProetale
        (Type (max (u + 1) v)) X.smallEtaleTopology (Scheme.ProEt.topology X)).unit.app F))
  obtain ⟨j, f, hjf⟩ := Scheme.proetaleInverseImage_exists_map_eq_of_isLimit.{u, v} X
    (Y ⋙ X.etaleToProetale) c hc (fun f => haffine f) hqc F i
    (e.hom.app (op (Y.obj i)) s) (e.hom.app (op (Y.obj i)) t) hst
  exact ⟨j, f, (map_hom_app_eq_iff_of_iso e _ s t).1 hjf⟩

end AlgebraicGeometry

end
