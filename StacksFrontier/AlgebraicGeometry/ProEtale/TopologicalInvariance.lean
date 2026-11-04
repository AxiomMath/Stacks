module

public import Mathlib.Algebra.Category.Ring.FinitePresentation
public import Mathlib.AlgebraicGeometry.Morphisms.UniversallyInjective
public import Mathlib.CategoryTheory.Adjunction.Mates
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocalProperties
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvarianceAffine
public import StacksFrontier.AlgebraicGeometry.Morphisms.UniversalHomeomorphism.Defs.Integral
public import StacksFrontier.AlgebraicGeometry.Morphisms.WeaklyEtale.IndEtale
public import StacksFrontier.AlgebraicGeometry.ProEtale.Site.AffineIndEtaleDense
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.SmallToBigTopos
public import StacksFrontier.AlgebraicGeometry.ProEtale.TopologicalInvarianceReduction
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.RingTheory.Etale.IndEtaleUniverse
public import StacksFrontier.AlgebraicGeometry.ProEtale.SiteFunctoriality.AffineIndEtaleLift

/-!
# Topological invariance of the small pro-étale topos

Let `f : T ⟶ S` be an integral, universally injective and surjective morphism of schemes in a
chosen big pro-étale site. The direct and inverse image functors of the induced morphism of
small pro-étale topoi are quasi-inverse equivalences. This is Stacks Project, Tag 09AB.

The proof follows the source. Both assertions are the same one, because the two functors are an
adjoint pair, so it suffices to show that the unit and the counit of that adjunction are
isomorphisms; and both are local on the target, the restriction of the unit and the counit to
the small pro-étale site of an affine open of `S` being computed by a square of base-change
functors whose mate is an isomorphism. This reduces the statement to an affine base, and then to
an affine `T` as well.

Over an affine base the small pro-étale topos is the topos of the affine ind-étale site, and base
change is an equivalence of that site with its counterpart over `T`. Global sections identify the
opposite of the affine ind-étale site with the category of ind-étale algebras over `Γ(S, ⊤)`, and
under that identification base change becomes extension of scalars along `Γ(S, ⊤) ⟶ Γ(T, ⊤)`.
Extension of scalars is an equivalence on étale algebras by topological invariance of the étale
site on affine objects, Stacks Project, Tag 05YX, and an equivalence on étale algebras extends to
one on ind-étale algebras because the étale algebras are finitely presentable objects. The
cardinality bookkeeping needed to stay inside the chosen big site is carried out on presentations
of étale algebras as quotients of polynomial rings. Finally the coverings of the two affine
ind-étale sites agree, because a family of affine objects is jointly surjective exactly when its
base change along the surjection `f` is, so base change is cocontinuous as well as continuous and
therefore induces an equivalence of sheaf categories.

## Main results

* `AlgebraicGeometry.ProEtale.smallProetalePushforward_isEquivalence` — the direct image of the
  induced morphism of small pro-étale topoi is an equivalence.
* `AlgebraicGeometry.ProEtale.smallProetaleInverseImage_isEquivalence` — so is the inverse image.
* `AlgebraicGeometry.ProEtale.smallProetaleMorphism_counit_isIso_of_affineOpen` — the counit of
  the adjunction is an isomorphism as soon as it is one after base change to every affine open of
  the target, which is the locality used in the reduction.

The packaged equivalence of the two functors is `CategoryTheory.Adjunction.toEquivalence` of the
adjunction `f⁻¹ ⊣ f_*`, whose unit and counit are isomorphisms once either functor is an
equivalence, so no separate declaration states that they are quasi-inverse.

## Implementation notes

The two reductions that are purely formal are taken from
`StacksFrontier.AlgebraicGeometry.ProEtale.TopologicalInvarianceReduction`: the inverse-image
assertion is deduced from the direct-image one by
`AlgebraicGeometry.ProEtale.smallProetaleInverseImage_isEquivalence_of_pushforward`. The
site-level criterion recorded there,
`AlgebraicGeometry.ProEtale.smallProetalePushforward_isEquivalence_of_isDenseSubsite`, is not
used: base change is not exhibited here as a dense subsite inclusion of the small pro-étale site
of `S` in that of `T`, but as an equivalence of the two affine ind-étale subsites, which is a
different and weaker route to the same conclusion.

Two results cited by the source are not available in this library and occur as explicit
hypotheses of every statement that needs them, so that nothing here is weaker than it looks.

* Essential surjectivity of base change on small étale sites along an arbitrary universal
  homeomorphism, which is the only remaining content of Stacks Project, Tag 04DZ; its full and
  faithful halves are proved in
  `StacksFrontier.AlgebraicGeometry.EtaleCohomology.TopologicalInvariance`.
* `AlgebraicGeometry.IntegralHasFinitePresentationLimit`, which is Stacks Project, Tag 09YZ over
  a quasi-compact quasi-separated base, and is what Stacks Project, Tag 05YU still needs.

Both enter at a single place, the appeal to
`Stacks.Etale.affineEtalePullback_isEquivalence_of_essSurj_of_h09YZ` inside
`AlgebraicGeometry.ProEtale.etalePushout_isEquivalence`, and are threaded unchanged from there to
the two main results.

The local criterion for the unit and the counit is an application of the calculus of mates: the
square of base-change functors over an open immersion `U ⟶ S` commutes up to a canonical
isomorphism, its mate for the adjunctions between pushforward along the open immersion and base
change along it is again an isomorphism, and the mate calculus then rewrites the restriction of
the unit and of the counit in terms of the unit and the counit over `U`.

## References

* [Stacks Project, Tag 09AB](https://stacks.math.columbia.edu/tag/09AB)
* [Stacks Project, Tag 098K](https://stacks.math.columbia.edu/tag/098K)
* [Stacks Project, Tag 098T](https://stacks.math.columbia.edu/tag/098T)
* [Stacks Project, Tag 098X](https://stacks.math.columbia.edu/tag/098X)
* [Stacks Project, Tag 04DZ](https://stacks.math.columbia.edu/tag/04DZ)
* [Stacks Project, Tag 05YX](https://stacks.math.columbia.edu/tag/05YX)
* [Stacks Project, Tag 05YU](https://stacks.math.columbia.edu/tag/05YU)
* [Stacks Project, Tag 09YZ](https://stacks.math.columbia.edu/tag/09YZ)
-/

@[expose] public section

open AlgebraicGeometry CategoryTheory

open CategoryTheory.Limits
open scoped AlgebraicGeometry

universe u w v₁ v₂ u₁ u₂ v₃ v₄ u₃ u₄

namespace AlgebraicGeometry.ProEtale

private def sheafSquare
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {F : Type u₄} [Category.{v₄} F]
    {G : C ⥤ E} {H : D ⥤ F} {L : C ⥤ D} {M : E ⥤ F}
    {A : Type w} [Category A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (J' : GrothendieckTopology E) (K' : GrothendieckTopology F)
    [G.IsContinuous J J'] [H.IsContinuous K K']
    [L.IsContinuous J K] [M.IsContinuous J' K']
    (α : G ⋙ M ⟶ L ⋙ H) :
    H.sheafPushforwardContinuous A K K' ⋙
      L.sheafPushforwardContinuous A J K ⟶
    M.sheafPushforwardContinuous A J' K' ⋙
      G.sheafPushforwardContinuous A J J' where
  app P := { hom := {
    app X := P.obj.map (α.app X.unop).op
    naturality X Y f := by
      change P.obj.map (H.map (L.map f.unop)).op ≫ _ =
        _ ≫ P.obj.map (M.map (G.map f.unop)).op
      rw [← P.obj.map_comp, ← P.obj.map_comp, ← op_comp, ← op_comp]
      congr 1
      exact congrArg Quiver.Hom.op (α.naturality f.unop).symm } }
  naturality P Q f := by
    ext X
    exact (f.hom.naturality (α.app X.unop).op).symm

private lemma sheafSquare_isIso
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {F : Type u₄} [Category.{v₄} F]
    {G : C ⥤ E} {H : D ⥤ F} {L : C ⥤ D} {M : E ⥤ F}
    {A : Type w} [Category A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (J' : GrothendieckTopology E) (K' : GrothendieckTopology F)
    [G.IsContinuous J J'] [H.IsContinuous K K']
    [L.IsContinuous J K] [M.IsContinuous J' K']
    (α : G ⋙ M ⟶ L ⋙ H) [IsIso α] :
    IsIso (sheafSquare (A := A) J K J' K' α) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro P
  rw [← ObjectProperty.isIso_hom_iff]
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro X
  change IsIso (P.obj.map (α.app X.unop).op)
  infer_instance

private lemma sheafSquare_mate
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {F : Type u₄} [Category.{v₄} F]
    {G : C ⥤ E} {H : D ⥤ F} {L : C ⥤ D} {M : E ⥤ F}
    {R : D ⥤ C} {N : F ⥤ E} (a : L ⊣ R) (b : M ⊣ N)
    {A : Type w} [Category A]
    (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    (J' : GrothendieckTopology E) (K' : GrothendieckTopology F)
    [G.IsContinuous J J'] [H.IsContinuous K K']
    [L.IsContinuous J K] [M.IsContinuous J' K']
    [R.IsContinuous K J] [N.IsContinuous K' J']
    (α : G ⋙ M ⟶ L ⋙ H) :
    (mateEquiv (b.sheafPushforwardContinuous J' K')
      (a.sheafPushforwardContinuous J K)
      (TwoSquare.mk _ _ _ _ (sheafSquare (A := A) J K J' K' α))).natTrans =
    sheafSquare K K' J J'
      (mateEquiv a b (TwoSquare.mk _ _ _ _ α)).natTrans := by
  ext P X
  simp [mateEquiv, sheafSquare]
  rfl

/-- The iterated mate of an isomorphism is an isomorphism: transposing twice turns the mate
construction into conjugation, under which an isomorphism stays one. -/
private lemma isIso_iterated_mate_symm
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {F : Type u₄} [Category.{v₄} F]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {L' : E ⥤ F} {R' : F ⥤ E} (adj' : L' ⊣ R')
    {G : C ⥤ E} {U : E ⥤ C} (aG : G ⊣ U)
    {H : D ⥤ F} {V : F ⥤ D} (aH : H ⊣ V)
    (γ : V ⋙ R ≅ R' ⋙ U) :
    IsIso ((mateEquiv adj adj').symm
      ((mateEquiv aH aG).symm (TwoSquare.mk _ _ _ _ γ.hom))).natTrans := by
  rw [iterated_mateEquiv_conjugateEquiv_symm adj adj' aG aH (TwoSquare.mk _ _ _ _ γ.hom)]
  change IsIso ((conjugateEquiv (adj.comp aH) (aG.comp adj')).symm γ.hom)
  infer_instance

private lemma isIso_local_counit
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {F : Type u₄} [Category.{v₄} F]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {L' : E ⥤ F} {R' : F ⥤ E} (adj' : L' ⊣ R')
    {G : C ⥤ E} {U : E ⥤ C} (aG : G ⊣ U)
    {H : D ⥤ F} {V : F ⥤ D} (aH : H ⊣ V)
    (γ : V ⋙ R ≅ R' ⋙ U)
    [IsIso adj'.counit]
    (hmate : IsIso (((mateEquiv aH aG).symm (TwoSquare.mk _ _ _ _ γ.hom)).natTrans)) :
    ∀ Y, IsIso (H.map (adj.counit.app Y)) := by
  let α := (mateEquiv aH aG).symm (TwoSquare.mk _ _ _ _ γ.hom)
  let β := (mateEquiv adj adj').symm α
  intro Y
  have : IsIso (β.app (R.obj Y)) :=
    (NatTrans.isIso_iff_isIso_app _).mp (isIso_iterated_mate_symm adj adj' aG aH γ) _
  have : IsIso (α.app Y) :=
    (NatTrans.isIso_iff_isIso_app _).mp hmate _
  have : IsIso (adj'.counit.app (H.obj Y)) :=
    (NatTrans.isIso_iff_isIso_app _).mp inferInstance _
  have hi : IsIso (β.app (R.obj Y) ≫ H.map (adj.counit.app Y)) := by
    rw [← mateEquiv_counit_symm adj adj' α Y]
    infer_instance
  exact IsIso.of_isIso_comp_left (β.app (R.obj Y)) _

private lemma isIso_local_unit_counit
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    {E : Type u₃} [Category.{v₃} E] {F : Type u₄} [Category.{v₄} F]
    {L : C ⥤ D} {R : D ⥤ C} (adj : L ⊣ R)
    {L' : E ⥤ F} {R' : F ⥤ E} (adj' : L' ⊣ R')
    {G : C ⥤ E} {U : E ⥤ C} (aG : G ⊣ U)
    {H : D ⥤ F} {V : F ⥤ D} (aH : H ⊣ V)
    (γ : V ⋙ R ≅ R' ⋙ U)
    [R'.IsEquivalence]
    (hmate : IsIso (((mateEquiv aH aG).symm (TwoSquare.mk _ _ _ _ γ.hom)).natTrans)) :
    (∀ X, IsIso (G.map (adj.unit.app X))) ∧
      (∀ Y, IsIso (H.map (adj.counit.app Y))) := by
  let α := (mateEquiv aH aG).symm (TwoSquare.mk _ _ _ _ γ.hom)
  let β := (mateEquiv adj adj').symm α
  have : IsIso α.natTrans := hmate
  refine ⟨fun X ↦ ?_, isIso_local_counit adj adj' aG aH γ hmate⟩
  have : IsIso (β.app X) :=
    (NatTrans.isIso_iff_isIso_app _).mp (isIso_iterated_mate_symm adj adj' aG aH γ) _
  have : IsIso (α.app (L.obj X)) := (NatTrans.isIso_iff_isIso_app _).mp hmate _
  have hi : IsIso (G.map (adj.unit.app X) ≫ α.app (L.obj X)) := by
    rw [unit_mateEquiv_symm adj adj' α X]
    change IsIso (adj'.unit.app (G.obj X) ≫ R'.map (β.app X))
    infer_instance
  exact IsIso.of_isIso_comp_right _ (α.app (L.obj X))

private lemma map_bijective_of_ind_target
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty C) (F : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{w, w} F]
    (hP : ∀ X, P X → IsFinitelyPresentable.{w} X)
    (hFP : ∀ X, P X → IsFinitelyPresentable.{w} (F.obj X))
    (hF : ∀ X Y, P X → P Y → Function.Bijective (F.map : (X ⟶ Y) → _))
    {X Y : C} (hX : P X) (hY : P.ind.{w} Y) :
    Function.Bijective (F.map : (X ⟶ Y) → _) := by
  have := hP X hX
  have := hFP X hX
  obtain ⟨J, _, _, p, hp⟩ := hY
  constructor
  · intro f g hfg
    obtain ⟨i, f', hf⟩ := IsFinitelyPresentable.exists_hom_of_isColimit p.isColimit f
    obtain ⟨j, g', hg⟩ := IsFinitelyPresentable.exists_hom_of_isColimit p.isColimit g
    have hh : F.map f' ≫ F.map (p.ι.app i) = F.map g' ≫ F.map (p.ι.app j) := by
      simpa only [← F.map_comp, hf, hg] using hfg
    obtain ⟨k, a, b, hab⟩ :=
      IsFinitelyPresentable.exists_eq_of_isColimit (isColimitOfPreserves F p.isColimit) _ _ hh
    have heq : f' ≫ p.diag.map a = g' ≫ p.diag.map b :=
      (hF X (p.diag.obj k) hX (hp k)).1 (by simpa only [Functor.comp_map, F.map_comp] using hab)
    rw [← hf, ← hg, ← p.w a, ← p.w b, ← Category.assoc, ← Category.assoc, heq]
  · intro f
    obtain ⟨i, f', hf⟩ :=
      IsFinitelyPresentable.exists_hom_of_isColimit (isColimitOfPreserves F p.isColimit) f
    obtain ⟨g, hg⟩ := (hF X (p.diag.obj i) hX (hp i)).2 f'
    refine ⟨g ≫ p.ι.app i, ?_⟩
    change f' ≫ F.map (p.ι.app i) = f at hf
    simpa only [F.map_comp, hg] using hf

private lemma map_bijective_of_ind
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty C) (F : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{w, w} F]
    (hP : ∀ X, P X → IsFinitelyPresentable.{w} X)
    (hFP : ∀ X, P X → IsFinitelyPresentable.{w} (F.obj X))
    (hF : ∀ X Y, P X → P Y → Function.Bijective (F.map : (X ⟶ Y) → _))
    {X Y : C} (hX : P.ind.{w} X) (hY : P.ind.{w} Y) :
    Function.Bijective (F.map : (X ⟶ Y) → _) := by
  classical
  obtain ⟨J, _, _, p, hp⟩ := hX
  have bij (j : J) := map_bijective_of_ind_target P F hP hFP hF (hp j) hY
  constructor
  · intro f g hfg
    exact p.isColimit.hom_ext fun j ↦ (bij j).1 (by simp only [F.map_comp, hfg])
  · intro f
    choose g hg using fun j ↦ (bij j).2 (F.map (p.ι.app j) ≫ f)
    let c : Cocone p.diag :=
      { pt := Y
        ι :=
          { app := g
            naturality := by
              intro i j a
              dsimp
              rw [Category.comp_id]
              apply (bij i).1
              rw [F.map_comp, hg j, ← Category.assoc, ← F.map_comp, p.w, hg i] } }
    refine ⟨p.isColimit.desc c, ?_⟩
    refine (isColimitOfPreserves F p.isColimit).hom_ext fun j ↦ ?_
    change F.map (p.ι.app j) ≫ F.map (p.isColimit.desc c) = F.map (p.ι.app j) ≫ f
    rw [← F.map_comp, p.isColimit.fac]
    exact hg j

private lemma exists_ind_preimage
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    [HasFilteredColimitsOfSize.{w, w} C]
    [PreservesFilteredColimitsOfSize.{w, w} F]
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    [(Q.lift (P.ι ⋙ F) hF).IsEquivalence]
    {Y : D} (hY : Q.ind.{w} Y) :
    ∃ X : C, P.ind.{w} X ∧ Nonempty (F.obj X ≅ Y) := by
  classical
  let G := Q.lift (P.ι ⋙ F) hF
  let e := G.asEquivalence
  obtain ⟨J, _, _, p, hp⟩ := hY
  let q : J ⥤ Q.FullSubcategory := Q.lift p.diag hp
  let d : J ⥤ C := q ⋙ e.inverse ⋙ P.ι
  have hd (j : J) : P (d.obj j) := (e.inverse.obj (q.obj j)).property
  refine ⟨colimit d, ⟨J, inferInstance, inferInstance, .colimit d, hd⟩, ?_⟩
  let α : d ⋙ F ≅ p.diag := NatIso.ofComponents
    (fun j ↦ Q.ι.mapIso (e.counitIso.app (q.obj j))) (by
      intro i j a
      exact congrArg (fun t ↦ Q.ι.map t) (e.counitIso.hom.naturality (q.map a)))
  let p' := ((ColimitPresentation.colimit d).map F).changeDiag α.symm
  exact ⟨p'.isColimit.coconePointUniqueUpToIso p.isColimit⟩

private lemma ind_map
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    [PreservesFilteredColimitsOfSize.{w, w} F]
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    (X : P.ind.{w}.FullSubcategory) : Q.ind.{w} (F.obj X.obj) := by
  obtain ⟨J, _, _, p, hp⟩ := X.property
  exact ⟨J, inferInstance, inferInstance, p.map F, fun j ↦ hF ⟨_, hp j⟩⟩

private lemma isEquivalence_ind_lift
    {C : Type u₁} [Category.{v₁} C] {D : Type u₂} [Category.{v₂} D]
    (P : ObjectProperty C) (Q : ObjectProperty D) (F : C ⥤ D)
    [HasFilteredColimitsOfSize.{w, w} C]
    [PreservesFilteredColimitsOfSize.{w, w} F]
    (hP : ∀ X, P X → IsFinitelyPresentable.{w} X)
    (hFP : ∀ X, P X → IsFinitelyPresentable.{w} (F.obj X))
    (hF : ∀ X : P.FullSubcategory, Q (F.obj X.obj))
    [(Q.lift (P.ι ⋙ F) hF).IsEquivalence] :
    (Q.ind.{w}.lift (P.ind.{w}.ι ⋙ F) (ind_map P Q F hF)).IsEquivalence := by
  let G := Q.lift (P.ι ⋙ F) hF
  have bij (X Y : C) (hX : P X) (hY : P Y) :
      Function.Bijective (F.map : (X ⟶ Y) → _) := by
    constructor
    · intro a b hab
      have hh : G.map (ObjectProperty.homMk (X := ⟨X, hX⟩) (Y := ⟨Y, hY⟩) a) =
          G.map (ObjectProperty.homMk b) := ObjectProperty.hom_ext _ hab
      exact congrArg (fun t ↦ t.hom) (G.map_injective hh)
    · intro a
      obtain ⟨b, hb⟩ := G.map_surjective
        (ObjectProperty.homMk (X := G.obj ⟨X, hX⟩) (Y := G.obj ⟨Y, hY⟩) a)
      exact ⟨b.hom, congrArg (fun t ↦ t.hom) hb⟩
  let H := Q.ind.{w}.lift (P.ind.{w}.ι ⋙ F) (ind_map P Q F hF)
  have hbij (X Y : P.ind.{w}.FullSubcategory) :=
    map_bijective_of_ind P F hP hFP bij X.property Y.property
  have : H.Full := ⟨fun {X Y} a ↦ by
    obtain ⟨b, hb⟩ := (hbij X Y).2 a.hom
    exact ⟨ObjectProperty.homMk b, ObjectProperty.hom_ext _ hb⟩⟩
  have : H.Faithful := ⟨fun {X Y} a b hab ↦
    ObjectProperty.hom_ext _ ((hbij X Y).1 (congrArg (fun t ↦ t.hom) hab))⟩
  have : H.EssSurj := ⟨fun Y ↦ by
    obtain ⟨X, hX, ⟨e⟩⟩ := exists_ind_preimage P Q F hF Y.property
    exact ⟨⟨X, hX⟩, ⟨Q.ind.isoMk e⟩⟩⟩
  change H.IsEquivalence
  exact {}

section AffineEtaleComparison

open Opposite

private abbrev EtaleUnderCat (A : CommRingCat.{u}) :=
  (CommRingCat.etale.underObj (X := A)).FullSubcategory

private abbrev AffineEtaleObj (S : Scheme.{u}) :=
  ObjectProperty.FullSubcategory (fun U : S.Etale ↦ IsAffine U.left)

private noncomputable def etaleSpec (A : CommRingCat.{u}) :
    (EtaleUnderCat A)ᵒᵖ ⥤ AffineEtaleObj (Spec A) where
  obj X := ⟨MorphismProperty.Over.mk ⊤ (Spec.map X.unop.obj.hom)
    ((HasRingHomProperty.Spec_iff (P := @Etale)).2 X.unop.property),
    inferInstanceAs (IsAffine (Spec X.unop.obj.right))⟩
  map {X Y} f := ObjectProperty.homMk <|
    MorphismProperty.Over.homMk (Spec.map f.unop.hom.right) (by
      change Spec.map f.unop.hom.right ≫ Spec.map Y.unop.obj.hom =
        Spec.map X.unop.obj.hom
      rw [← Spec.map_comp, Under.w])
  map_id X := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact Spec.map_id _
  map_comp f g := by
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact Spec.map_comp _ _

private lemma etaleSpec_map_bijective (A : CommRingCat.{u})
    (X Y : (EtaleUnderCat A)ᵒᵖ) :
    Function.Bijective ((etaleSpec A).map : (X ⟶ Y) → _) := by
  constructor
  · intro a b hab
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    apply Spec.map_injective
    exact congrArg (fun t ↦ t.hom.left) hab
  · intro a
    let g := Spec.homEquiv a.hom.left
    have hg : Spec.map g = a.hom.left := Spec.homEquiv.symm_apply_apply _
    have hw : Y.unop.obj.hom ≫ g = X.unop.obj.hom := by
      apply Spec.map_injective
      rw [Spec.map_comp, hg]
      exact MorphismProperty.Over.w a.hom
    refine ⟨(ObjectProperty.homMk (Under.homMk g hw)).op, ?_⟩
    apply ObjectProperty.hom_ext
    apply MorphismProperty.Over.Hom.ext
    exact hg

private lemma etaleSpec_essSurj (A : CommRingCat.{u}) : (etaleSpec A).EssSurj := by
  constructor
  intro U
  have : IsAffine U.obj.left := U.property
  have : Etale U.obj.hom := U.obj.prop
  let h : A ⟶ Γ(U.obj.left, ⊤) := (Scheme.ΓSpecIso A).inv ≫ U.obj.hom.appTop
  let e : Spec Γ(U.obj.left, ⊤) ≅ U.obj.left := (asIso U.obj.left.toSpecΓ).symm
  have hw : e.hom ≫ U.obj.hom = Spec.map h := by
    apply (cancel_epi U.obj.left.toSpecΓ).mp
    dsimp [e, h]
    simp only [Spec.map_comp, ← Category.assoc, ← Scheme.toSpecΓ_naturality]
    simp
  have hh : CommRingCat.etale h := by
    apply (HasRingHomProperty.Spec_iff (P := @Etale)).1
    rw [← hw]
    infer_instance
  exact ⟨op (⟨Under.mk h, hh⟩ : EtaleUnderCat A),
    ⟨ObjectProperty.isoMk _ (MorphismProperty.Over.isoMk e hw)⟩⟩

private lemma etaleSpec_isEquivalence (A : CommRingCat.{u}) :
    (etaleSpec A).IsEquivalence where
  faithful := ⟨fun {X Y} ↦ (etaleSpec_map_bijective A X Y).1⟩
  full := ⟨fun {X Y} ↦ (etaleSpec_map_bijective A X Y).2⟩
  essSurj := etaleSpec_essSurj A

private noncomputable def etalePushout {A B : CommRingCat.{u}} (f : A ⟶ B) :
    EtaleUnderCat A ⥤ EtaleUnderCat B :=
  (CommRingCat.etale.underObj).lift
    ((CommRingCat.etale.underObj (X := A)).ι ⋙ Under.pushout f)
    (fun X ↦ CommRingCat.etale.pushout_inr X.obj.hom f X.property)

private noncomputable abbrev specEtalePullback {A B : CommRingCat.{u}} (f : A ⟶ B)
    [MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) (Spec.map f)]
    [MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) (Spec.map f)] :
    (Spec A).Etale ⥤ (Spec B).Etale :=
  MorphismProperty.Over.pullback (@Etale : MorphismProperty Scheme.{u}) ⊤ (Spec.map f)

private noncomputable def etaleSpecPushoutIso
    {A B : CommRingCat.{u}} (f : A ⟶ B)
    [MorphismProperty.HasPullbacksAlong (@Etale : MorphismProperty Scheme.{u}) (Spec.map f)]
    [MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) (Spec.map f)]
    (h : ∀ U : AffineEtaleObj (Spec A),
      IsAffine ((specEtalePullback f).obj U.obj).left) :
    (etalePushout f).op ⋙ etaleSpec B ≅
      etaleSpec A ⋙ ObjectProperty.lift (fun U : (Spec B).Etale ↦ IsAffine U.left)
        ((ObjectProperty.ι (fun U : (Spec A).Etale ↦ IsAffine U.left)) ⋙
          specEtalePullback f)
        h := by
  refine NatIso.ofComponents (fun X ↦ ObjectProperty.isoMk _
    (MorphismProperty.Over.isoMk
      (isPullback_SpecMap_pushout X.unop.obj.hom f).isoPullback
      (IsPullback.isoPullback_hom_snd _))) ?_
  intro X Y a
  apply ObjectProperty.hom_ext
  apply MorphismProperty.Over.Hom.ext
  have har : Spec.map (Under.Hom.right a.unop.hom) ≫ Spec.map Y.unop.obj.hom =
      Spec.map X.unop.obj.hom := by
    rw [← Spec.map_comp, Under.w]
  have hw : (pullback.fst (Spec.map X.unop.obj.hom) (Spec.map f) ≫
        Spec.map (Under.Hom.right a.unop.hom)) ≫ Spec.map Y.unop.obj.hom =
      pullback.snd (Spec.map X.unop.obj.hom) (Spec.map f) ≫ Spec.map f := by
    rw [Category.assoc, har]
    exact pullback.condition
  change Spec.map (pushout.desc (Under.Hom.right a.unop.hom ≫ pushout.inl _ _)
        (pushout.inr _ _) (by simp [← pushout.condition])) ≫
      (isPullback_SpecMap_pushout Y.unop.obj.hom f).isoPullback.hom =
    (isPullback_SpecMap_pushout X.unop.obj.hom f).isoPullback.hom ≫
      pullback.lift (pullback.fst (Spec.map X.unop.obj.hom) (Spec.map f) ≫
          Spec.map (Under.Hom.right a.unop.hom))
        (pullback.snd (Spec.map X.unop.obj.hom) (Spec.map f)) hw
  apply pullback.hom_ext
  · rw [Category.assoc, IsPullback.isoPullback_hom_fst, ← Spec.map_comp, pushout.inl_desc,
      Spec.map_comp, Category.assoc, pullback.lift_fst, ← Category.assoc,
      IsPullback.isoPullback_hom_fst]
  · rw [Category.assoc, IsPullback.isoPullback_hom_snd, ← Spec.map_comp, pushout.inr_desc,
      Category.assoc, pullback.lift_snd, IsPullback.isoPullback_hom_snd]

variable
  (h04DZ : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), UniversalHomeomorphism g →
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) g := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) g :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    (show Y.Etale ⥤ X.Etale from
      MorphismProperty.Over.pullback
        (@Etale : MorphismProperty Scheme.{u}) ⊤ g).EssSurj)
  (h09YZ : IntegralHasFinitePresentationLimit.{u})

include h04DZ h09YZ in
private lemma etalePushout_isEquivalence {A B : CommRingCat.{u}} (f : A ⟶ B)
    [UniversalHomeomorphism (Spec.map f)] :
    (etalePushout f).IsEquivalence := by
  have : MorphismProperty.HasPullbacksAlong
      (@Etale : MorphismProperty Scheme.{u}) (Spec.map f) := ⟨fun _ _ ↦ inferInstance⟩
  have : MorphismProperty.IsStableUnderBaseChangeAlong
      (@Etale : MorphismProperty Scheme.{u}) (Spec.map f) :=
    ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
  obtain ⟨h, hh⟩ :=
    Stacks.Etale.affineEtalePullback_isEquivalence_of_essSurj_of_h09YZ (Spec.map f)
      (h04DZ (Spec.map f) inferInstance) h09YZ
  let G := ObjectProperty.lift (fun U : (Spec B).Etale ↦ IsAffine U.left)
    ((ObjectProperty.ι (fun U : (Spec A).Etale ↦ IsAffine U.left)) ⋙
      specEtalePullback f) h
  have : G.IsEquivalence := hh
  have : (etaleSpec A).IsEquivalence := etaleSpec_isEquivalence A
  have : (etaleSpec B).IsEquivalence := etaleSpec_isEquivalence B
  have : ((etalePushout f).op ⋙ etaleSpec B).IsEquivalence :=
    Functor.isEquivalence_of_iso (etaleSpecPushoutIso f h).symm
  have : (etalePushout f).op.IsEquivalence :=
    Functor.isEquivalence_of_comp_right _ (etaleSpec B)
  have : (etalePushout f).op.unop.IsEquivalence :=
    (etalePushout f).op.asEquivalence.unop.isEquivalence_functor
  exact Functor.isEquivalence_of_iso (etalePushout f).opUnopIso

private abbrev IndEtaleUnder (A : CommRingCat.{u}) :=
  (CommRingCat.etale.underObj (X := A)).ind.{u}.FullSubcategory

private noncomputable def indEtalePushout {A B : CommRingCat.{u}} (f : A ⟶ B) :
    IndEtaleUnder A ⥤ IndEtaleUnder B :=
  (CommRingCat.etale.underObj (X := B)).ind.{u}.lift
    ((CommRingCat.etale.underObj (X := A)).ind.{u}.ι ⋙ Under.pushout f)
    (ind_map _ _ (Under.pushout f)
      (fun X ↦ CommRingCat.etale.pushout_inr X.obj.hom f X.property))

include h04DZ h09YZ in
private lemma indEtalePushout_isEquivalence {A B : CommRingCat.{u}} (f : A ⟶ B)
    [UniversalHomeomorphism (Spec.map f)] :
    (indEtalePushout f).IsEquivalence := by
  unfold indEtalePushout
  have : ((CommRingCat.etale.underObj (X := B)).lift
      ((CommRingCat.etale.underObj (X := A)).ι ⋙ Under.pushout f)
      (fun X ↦ CommRingCat.etale.pushout_inr X.obj.hom f X.property)).IsEquivalence :=
    etalePushout_isEquivalence h04DZ h09YZ f
  exact isEquivalence_ind_lift.{u, u, u, u + 1, u + 1} (CommRingCat.etale.underObj (X := A))
    (CommRingCat.etale.underObj (X := B)) (Under.pushout f)
    (fun X hX ↦ CommRingCat.isFinitelyPresentable_under A X
      (show RingHom.Etale X.hom.hom from hX).finitePresentation)
    (fun X hX ↦ CommRingCat.isFinitelyPresentable_under B _
      (show RingHom.Etale ((Under.pushout f).obj X).hom.hom from
        CommRingCat.etale.pushout_inr X.hom f hX).finitePresentation)
    (fun X ↦ CommRingCat.etale.pushout_inr X.obj.hom f X.property)

private abbrev EtaleUnderPresentation (A : CommRingCat.{u}) :=
  Σ n : ℕ, { I : Ideal (MvPolynomial (Fin n) A) //
    (algebraMap A (MvPolynomial (Fin n) A ⧸ I)).Etale }

private noncomputable abbrev etaleUnderOfPresentation (A : CommRingCat.{u})
    (p : EtaleUnderPresentation A) : EtaleUnderCat A :=
  ⟨Under.mk (CommRingCat.ofHom (algebraMap A (MvPolynomial (Fin p.1) A ⧸ p.2.1))),
    p.2.2⟩

private lemma etaleUnder_exists_presentation {A : CommRingCat.{u}} (X : EtaleUnderCat A) :
    ∃ p : EtaleUnderPresentation A, Nonempty (etaleUnderOfPresentation A p ≅ X) := by
  let := X.obj.hom.hom.toAlgebra
  have : Algebra.Etale A X.obj.right := X.property
  obtain ⟨n, g, hg⟩ := (Algebra.FiniteType.iff_quotient_mvPolynomial''
    (R := A) (S := X.obj.right)).mp inferInstance
  let e := Ideal.quotientKerAlgEquivOfSurjective hg
  let Y : Under A := Under.mk (CommRingCat.ofHom
    (algebraMap A (MvPolynomial (Fin n) A ⧸ RingHom.ker g.toRingHom)))
  let ee : Y ≅ X.obj := Under.isoMk e.toRingEquiv.toCommRingCatIso (by
    apply CommRingCat.hom_ext
    ext a
    exact e.commutes a)
  have hY : (algebraMap A (MvPolynomial (Fin n) A ⧸ RingHom.ker g.toRingHom)).Etale :=
    (CommRingCat.etale.underObj (X := A)).prop_of_iso ee.symm X.property
  exact ⟨⟨n, ⟨RingHom.ker g.toRingHom, hY⟩⟩, ⟨ObjectProperty.isoMk _ ee⟩⟩

private lemma indEtaleUnder_jointly_surjective {A : CommRingCat.{u}}
    (C : IndEtaleUnder A) :
    Function.Surjective (fun t : Σ p : EtaleUnderPresentation A,
      ((etaleUnderOfPresentation A p).obj ⟶ C.obj) ×
        (etaleUnderOfPresentation A p).obj.right ↦ t.2.1.right t.2.2) := by
  intro x
  obtain ⟨J, _, _, p, hp⟩ := C.property
  obtain ⟨j, y, hy⟩ := Concrete.isColimit_exists_rep (p.diag ⋙ Under.forget A)
    (isColimitOfPreserves (Under.forget A) p.isColimit) x
  obtain ⟨q, ⟨e⟩⟩ := etaleUnder_exists_presentation (⟨p.diag.obj j, hp j⟩ : EtaleUnderCat A)
  refine ⟨⟨q, e.hom.hom ≫ p.ι.app j, e.inv.hom.right y⟩, ?_⟩
  change (p.ι.app j).right (e.hom.hom.right (e.inv.hom.right y)) = x
  have he := congrArg (fun t ↦ t.hom.right) e.inv_hom_id
  have hey := ConcreteCategory.congr_hom he y
  simpa only [CommRingCat.comp_apply, CommRingCat.id_apply] using hey ▸ hy

open Cardinal in
private lemma mk_etaleUnderPresentation_le (A : CommRingCat.{u}) (μ : Cardinal.{u})
    (hμ : Cardinal.aleph0 ≤ μ) (hA : Cardinal.mk A ≤ μ) :
    Cardinal.mk (EtaleUnderPresentation A) ≤ 2 ^ μ := by
  have hp (n : ℕ) : #(MvPolynomial (Fin n) A) ≤ μ :=
    (mk_le_of_algebra_finiteType A (MvPolynomial (Fin n) A)).trans (max_le hμ hA)
  have hI (n : ℕ) : #(Ideal (MvPolynomial (Fin n) A)) ≤ 2 ^ μ := by
    calc _ ≤ #(Set (MvPolynomial (Fin n) A)) :=
        mk_le_of_injective (SetLike.coe_injective (A := Ideal (MvPolynomial (Fin n) A)))
      _ = 2 ^ #(MvPolynomial (Fin n) A) := mk_set
      _ ≤ 2 ^ μ := power_le_power_left (by norm_num) (hp n)
  have hμ' : ℵ₀ ≤ 2 ^ μ := hμ.trans (cantor μ).le
  calc #(EtaleUnderPresentation A) =
      sum (fun n : ℕ ↦ #{I : Ideal (MvPolynomial (Fin n) A) //
        (algebraMap A (MvPolynomial (Fin n) A ⧸ I)).Etale}) := mk_sigma _
    _ ≤ sum (fun _ : ℕ ↦ 2 ^ μ) :=
      sum_le_sum _ _ (fun n ↦ (mk_subtype_le _).trans (hI n))
    _ = ℵ₀ * 2 ^ μ := by simp only [sum_const, mk_nat, lift_aleph0, lift_uzero]
    _ ≤ 2 ^ μ := (mul_le_mul' hμ' le_rfl).trans (by rw [mul_eq_self hμ'])

open Cardinal in
private lemma mk_indEtaleUnder_le {A D : CommRingCat.{u}} (f : A ⟶ D)
    (C : IndEtaleUnder A)
    (hF : ∀ X : EtaleUnderCat A,
      Function.Injective ((Under.pushout f).map : (X.obj ⟶ C.obj) → _))
    (μ : Cardinal.{u}) (hμ : Cardinal.aleph0 ≤ μ)
    (hA : Cardinal.mk A ≤ μ) (hD : Cardinal.mk D ≤ μ)
    (hC : Cardinal.mk ((Under.pushout f).obj C.obj).right ≤ μ) :
    Cardinal.mk C.obj.right ≤ 2 ^ μ := by
  have hQ (p : EtaleUnderPresentation A) : #(etaleUnderOfPresentation A p).obj.right ≤ μ :=
    (mk_le_of_algebra_finiteType A (MvPolynomial (Fin p.1) A ⧸ p.2.1)).trans
      (max_le hμ hA)
  have hPQ (p : EtaleUnderPresentation A) :
      #((Under.pushout f).obj (etaleUnderOfPresentation A p).obj).right ≤ μ := by
    let X := (Under.pushout f).obj (etaleUnderOfPresentation A p).obj
    let := X.hom.hom.toAlgebra
    have : Algebra.Etale D X.right :=
      CommRingCat.etale.pushout_inr (etaleUnderOfPresentation A p).obj.hom f p.2.2
    exact (mk_le_of_algebra_finiteType D X.right).trans (max_le hμ hD)
  have hhom (p : EtaleUnderPresentation A) :
      #((etaleUnderOfPresentation A p).obj ⟶ C.obj) ≤ 2 ^ μ := by
    let g : ((etaleUnderOfPresentation A p).obj ⟶ C.obj) →
        (((Under.pushout f).obj (etaleUnderOfPresentation A p).obj).right →
          ((Under.pushout f).obj C.obj).right) := fun a ↦ ((Under.pushout f).map a).right
    have hg : Function.Injective g := by
      intro a b hab
      apply hF _
      apply Under.UnderMorphism.ext
      apply CommRingCat.hom_ext
      exact RingHom.ext (congrFun hab)
    calc _ ≤ #(((Under.pushout f).obj (etaleUnderOfPresentation A p).obj).right →
          ((Under.pushout f).obj C.obj).right) := mk_le_of_injective hg
      _ = #((Under.pushout f).obj C.obj).right ^
        #((Under.pushout f).obj (etaleUnderOfPresentation A p).obj).right := by
          simp only [mk_arrow, lift_id]
      _ ≤ μ ^ #((Under.pushout f).obj (etaleUnderOfPresentation A p).obj).right :=
        power_le_power_right hC
      _ ≤ μ ^ μ := power_le_power_left (ne_of_gt (aleph0_pos.trans_le hμ)) (hPQ p)
      _ = 2 ^ μ := power_self_eq hμ
  have hμ' : ℵ₀ ≤ 2 ^ μ := hμ.trans (cantor μ).le
  calc #C.obj.right ≤ #(Σ p : EtaleUnderPresentation A,
        ((etaleUnderOfPresentation A p).obj ⟶ C.obj) ×
          (etaleUnderOfPresentation A p).obj.right) :=
      mk_le_of_surjective (indEtaleUnder_jointly_surjective C)
    _ = sum (fun p : EtaleUnderPresentation A ↦
        #(((etaleUnderOfPresentation A p).obj ⟶ C.obj) ×
          (etaleUnderOfPresentation A p).obj.right)) := mk_sigma _
    _ ≤ 2 ^ μ := sum_le_of_mk_le_of_forall_le hμ'
      (mk_etaleUnderPresentation_le A μ hμ hA) (fun p ↦ by
        rw [mk_prod, lift_id, lift_id]
        exact (mul_le_mul' (hhom p) ((hQ p).trans (cantor μ).le)).trans
          (by rw [mul_eq_self hμ']))

private lemma pushout_map_injective_of_faithful {A D : CommRingCat.{u}} (f : A ⟶ D)
    [(indEtalePushout f).Faithful] (C : IndEtaleUnder A) (X : EtaleUnderCat A) :
    Function.Injective ((Under.pushout f).map : (X.obj ⟶ C.obj) → _) := by
  intro a b hab
  let X' : IndEtaleUnder A :=
    ⟨X.obj, (CommRingCat.etale.underObj (X := A)).le_ind _ X.property⟩
  have he : (indEtalePushout f).map (ObjectProperty.homMk (X := X') (Y := C) a) =
      (indEtalePushout f).map (ObjectProperty.homMk b) := ObjectProperty.hom_ext _ hab
  exact congrArg (fun t ↦ t.hom) ((indEtalePushout f).map_injective he)

private lemma weaklyEtale_spec_of_ind {A D : CommRingCat.{u}} (f : A ⟶ D)
    (hf : (CommRingCat.etale.underObj (X := A)).ind.{u} (Under.mk f)) :
    WeaklyEtale (Spec.map f) := by
  let := f.hom.toAlgebra
  have h : (CommAlgCat.etale A).ind.{u} (CommAlgCat.of A D) :=
    CommAlgCat.ind_etale_iff_ind_algebraMap.mpr
      ((MorphismProperty.ind_iff_ind_underMk (P := CommRingCat.etale) f).mpr hf)
  have : Algebra.WeaklyEtale A D :=
    Algebra.weaklyEtale_of_ind_etale (StacksDraft.indEtale_iff.mpr h)
  constructor
  · apply (HasRingHomProperty.Spec_iff (P := @Flat)).mpr
    exact (RingHom.flat_algebraMap_iff).mpr inferInstance
  · change Flat (pullback.diagonal (Spec.map (CommRingCat.ofHom (algebraMap A D))))
    rw [diagonal_SpecMap A D]
    have hflat : Flat (Spec.map (CommRingCat.ofHom
        (Algebra.TensorProduct.lmul' A (S := D)).toRingHom)) :=
      (HasRingHomProperty.Spec_iff (P := @Flat)).mpr (Algebra.WeaklyEtale.flat_lmul' A D)
    exact MorphismProperty.comp_mem _ _ _ hflat inferInstance

end AffineEtaleComparison

variable
  (h04DZ : ∀ {X Y : Scheme.{u}} (g : X ⟶ Y), UniversalHomeomorphism g →
    letI : MorphismProperty.HasPullbacksAlong
        (@Etale : MorphismProperty Scheme.{u}) g := ⟨fun _ _ ↦ inferInstance⟩
    letI : MorphismProperty.IsStableUnderBaseChangeAlong
        (@Etale : MorphismProperty Scheme.{u}) g :=
      ⟨fun pb hg ↦ MorphismProperty.IsStableUnderBaseChange.of_isPullback pb hg⟩
    (show Y.Etale ⥤ X.Etale from
      MorphismProperty.Over.pullback
        (@Etale : MorphismProperty Scheme.{u}) ⊤ g).EssSurj)
  (h09YZ : IntegralHasFinitePresentationLimit.{u})

variable (B : BigProetaleSite.{u}) (T S : B.Scheme) (f : T ⟶ S)

private lemma isoSpec_inv_appTop_comp_ΓSpecIso_hom (Y : Scheme.{u}) [IsAffine Y] :
    Y.isoSpec.inv.appTop ≫ (Scheme.ΓSpecIso Γ(Y, ⊤)).hom = 𝟙 _ := by
  rw [← Scheme.toSpecΓ_appTop, ← Scheme.Hom.comp_appTop]
  simp

private lemma appTop_bijective {X Y : Scheme.{u}} [IsAffine Y] :
    Function.Bijective (Scheme.Hom.appTop : (X ⟶ Y) → _) := by
  refine ⟨fun _ _ h ↦ ext_of_isAffine h, fun g ↦ ?_⟩
  let h := ΓSpec.adjunction.homEquiv X (Opposite.op Γ(Y, ⊤)) g.op
  refine ⟨h ≫ Y.isoSpec.inv, ?_⟩
  rw [Scheme.Hom.comp_appTop]
  change Y.isoSpec.inv.appTop ≫ (ΓSpec.adjunction.homEquiv X _ g.op).appTop = g
  rw [ΓSpec_adjunction_homEquiv_eq, ← Category.assoc, isoSpec_inv_appTop_comp_ΓSpecIso_hom,
    Category.id_comp]

private noncomputable def affineIndEtaleGamma :
    (AffineIndEtaleProetale B S)ᵒᵖ ⥤ IndEtaleUnder Γ(S.obj, ⊤) where
  obj U := ⟨Under.mk (B.inclusion.map U.unop.obj.obj.hom).appTop, U.unop.property.2⟩
  map a := ObjectProperty.homMk (Under.homMk
    (B.inclusion.map a.unop.hom.hom.left).appTop (by
      change (B.inclusion.map _).appTop ≫ (B.inclusion.map _).appTop = _
      rw [← Scheme.Hom.comp_appTop, ← B.inclusion.map_comp, Over.w]
      rfl))
  map_id U := by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    simp
  map_comp a b := by
    apply ObjectProperty.hom_ext
    apply Under.UnderMorphism.ext
    simp

private lemma affineIndEtaleGamma_map_bijective [IsAffine S.obj]
    (U V : (AffineIndEtaleProetale B S)ᵒᵖ) :
    Function.Bijective ((affineIndEtaleGamma B S).map : (U ⟶ V) → _) := by
  have : IsAffine (B.inclusion.obj U.unop.obj.obj.left) := U.unop.property.1
  have : IsAffine (B.inclusion.obj V.unop.obj.obj.left) := V.unop.property.1
  have : IsAffine (B.inclusion.obj (⟨S.obj, S.property⟩ : B.Scheme)) :=
    inferInstanceAs (IsAffine S.obj)
  constructor
  · intro a b hab
    apply Quiver.Hom.unop_inj
    apply ObjectProperty.hom_ext
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply B.inclusion.map_injective
    exact ext_of_isAffine (congrArg (fun t ↦ t.hom.right) hab)
  · intro a
    obtain ⟨g, hg⟩ := (appTop_bijective (X := V.unop.obj.obj.left.obj)
      (Y := U.unop.obj.obj.left.obj)).2 a.hom.right
    have hw : g ≫ B.inclusion.map U.unop.obj.obj.hom =
        B.inclusion.map V.unop.obj.obj.hom := by
      apply ext_of_isAffine
      rw [Scheme.Hom.comp_appTop, hg]
      exact Under.w a.hom
    refine ⟨(ObjectProperty.homMk (ObjectProperty.homMk
      (Over.homMk (B.inclusion.preimage g) ?_))).op, ?_⟩
    · apply B.inclusion.map_injective
      simpa only [Functor.map_comp, Functor.map_preimage] using hw
    · apply ObjectProperty.hom_ext
      apply Under.UnderMorphism.ext
      change (B.inclusion.map (B.inclusion.preimage g)).appTop = _
      rw [Functor.map_preimage]
      exact hg

private noncomputable def affineIndEtaleGamma_fullyFaithful [IsAffine S.obj] :
    (affineIndEtaleGamma B S).FullyFaithful := by
  have : (affineIndEtaleGamma B S).Full :=
    ⟨fun {U V} ↦ (affineIndEtaleGamma_map_bijective B S U V).2⟩
  have : (affineIndEtaleGamma B S).Faithful :=
    ⟨fun {U V} ↦ (affineIndEtaleGamma_map_bijective B S U V).1⟩
  exact .ofFullyFaithful _

private lemma affineIndEtaleGamma_exists_preimage [IsAffine S.obj]
    (C : IndEtaleUnder Γ(S.obj, ⊤)) (hC : (Spec C.obj.right).size < B.cutoff) :
    ∃ U : (AffineIndEtaleProetale B S)ᵒᵖ,
      Nonempty ((affineIndEtaleGamma B S).obj U ≅ C) := by
  let g := Spec.map C.obj.hom ≫ S.obj.isoSpec.inv
  let e : Under.mk g.appTop ≅ C.obj :=
    Under.isoMk (Scheme.ΓSpecIso C.obj.right) (by
      dsimp only [g, Under.mk_hom]
      rw [Scheme.Hom.comp_appTop, Category.assoc, Scheme.ΓSpecIso_naturality,
        ← Category.assoc, isoSpec_inv_appTop_comp_ΓSpecIso_hom S.obj, Category.id_comp])
  have hwe : WeaklyEtale g := by
    have : WeaklyEtale (Spec.map C.obj.hom) := weaklyEtale_spec_of_ind C.obj.hom C.property
    infer_instance
  let U : AffineIndEtaleProetale B S :=
    ⟨⟨Over.mk (ObjectProperty.homMk (X := ⟨Spec C.obj.right, hC⟩) (Y := S) g), hwe⟩,
      inferInstanceAs (IsAffine (Spec C.obj.right)),
      (CommRingCat.etale.underObj (X := Γ(S.obj, ⊤))).ind.prop_of_iso e.symm C.property⟩
  exact ⟨Opposite.op U, ⟨ObjectProperty.isoMk _ e⟩⟩

private noncomputable def affineIndEtaleGammaBaseChangeIso
    [IsAffine S.obj] [IsAffine T.obj] :
    (affineIndEtaleBaseChange B f).op ⋙ affineIndEtaleGamma B T ≅
      affineIndEtaleGamma B S ⋙ indEtalePushout (B.inclusion.map f).appTop := by
  have : IsAffine (B.inclusion.obj S) := inferInstanceAs (IsAffine S.obj)
  have : IsAffine (B.inclusion.obj T) := inferInstanceAs (IsAffine T.obj)
  have : ∀ U : (AffineIndEtaleProetale B S)ᵒᵖ,
      IsAffine (B.inclusion.obj U.unop.obj.obj.left) := fun U ↦ U.unop.property.1
  refine NatIso.ofComponents (fun U ↦ ObjectProperty.isoMk _
    (Under.isoMk
      (isPushout_appTop_of_isPullback
        ((IsPullback.of_hasPullback U.unop.obj.obj.hom f).map B.inclusion)).isoPushout
      (IsPushout.inr_isoPushout_hom _))) ?_
  intro U V a
  apply ObjectProperty.hom_ext
  apply Under.UnderMorphism.ext
  apply (cancel_mono
    (isPushout_appTop_of_isPullback
      ((IsPullback.of_hasPullback V.unop.obj.obj.hom f).map B.inclusion)).isoPushout.inv).mp
  change (B.inclusion.map (pullback.map _ _ _ _ a.unop.hom.hom.left
      (𝟙 T) (𝟙 S) (by simp) (by simp))).appTop ≫
      (isPushout_appTop_of_isPullback
        ((IsPullback.of_hasPullback V.unop.obj.obj.hom f).map B.inclusion)).isoPushout.hom ≫
      (isPushout_appTop_of_isPullback
        ((IsPullback.of_hasPullback V.unop.obj.obj.hom f).map B.inclusion)).isoPushout.inv = _
  simp only [Iso.hom_inv_id, Category.comp_id]
  change _ = (isPushout_appTop_of_isPullback
      ((IsPullback.of_hasPullback U.unop.obj.obj.hom f).map B.inclusion)).isoPushout.hom ≫
    pushout.desc ((B.inclusion.map a.unop.hom.hom.left).appTop ≫ pushout.inl _ _)
      (pushout.inr _ _) _ ≫
      (isPushout_appTop_of_isPullback
        ((IsPullback.of_hasPullback V.unop.obj.obj.hom f).map B.inclusion)).isoPushout.inv
  have hV := isPushout_appTop_of_isPullback
    ((IsPullback.of_hasPullback V.unop.obj.obj.hom f).map B.inclusion)
  apply (isPushout_appTop_of_isPullback
    ((IsPullback.of_hasPullback U.unop.obj.obj.hom f).map B.inclusion)).hom_ext
  · simp only [← Category.assoc, IsPushout.inl_isoPushout_hom]
    simp only [Category.assoc]
    refine Eq.trans ?_ (pushout.inl_desc_assoc _ _ _ _).symm
    rw [Category.assoc, hV.inl_isoPushout_inv, ← Scheme.Hom.comp_appTop, ← Scheme.Hom.comp_appTop,
      ← B.inclusion.map_comp, ← B.inclusion.map_comp]
    congr 2
    exact pullback.lift_fst _ _ _
  · simp only [← Category.assoc, IsPushout.inr_isoPushout_hom]
    simp only [Category.assoc]
    refine Eq.trans ?_ (pushout.inr_desc_assoc _ _ _ _).symm
    rw [hV.inr_isoPushout_inv, ← Scheme.Hom.comp_appTop, ← B.inclusion.map_comp]
    congr 2
    exact pullback.lift_snd _ _ _

private lemma universalHomeomorphism_spec_appTop [IsAffine S.obj] [IsAffine T.obj]
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f)) :
    UniversalHomeomorphism (Spec.map (B.inclusion.map f).appTop) := by
  apply (universalHomeomorphism_iff_integral_universallyInjective_surjective _).2
  have : IsAffine (B.inclusion.obj S) := inferInstanceAs (IsAffine S.obj)
  have : IsAffine (B.inclusion.obj T) := inferInstanceAs (IsAffine T.obj)
  have hrInt : MorphismProperty.RespectsIso (@IsIntegralHom : MorphismProperty Scheme.{u}) :=
    MorphismProperty.RespectsIso.mk _
      (fun _ _ hg ↦ by have : IsIntegralHom _ := hg; exact inferInstance)
      (fun _ _ hg ↦ by have : IsIntegralHom _ := hg; exact inferInstance)
  have hrInj : MorphismProperty.RespectsIso (@UniversallyInjective : MorphismProperty Scheme.{u}) :=
    UniversallyInjective.respectsIso
  have e := arrowIsoSpecΓOfIsAffine (B.inclusion.map f)
  exact ⟨(MorphismProperty.arrow_mk_iso_iff (@IsIntegralHom) e).mp hIntegral,
    (MorphismProperty.arrow_mk_iso_iff (@UniversallyInjective) e).mp hInjective,
    (MorphismProperty.arrow_mk_iso_iff (@Surjective) e).mp hSurjective⟩

include h04DZ h09YZ in
private noncomputable def affineIndEtaleBaseChange_fullyFaithful
    [IsAffine S.obj] [IsAffine T.obj]
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f)) :
    (affineIndEtaleBaseChange B f).FullyFaithful := by
  have : UniversalHomeomorphism (Spec.map (B.inclusion.map f).appTop) :=
    universalHomeomorphism_spec_appTop B T S f hIntegral hInjective hSurjective
  have : (indEtalePushout (B.inclusion.map f).appTop).IsEquivalence :=
    indEtalePushout_isEquivalence h04DZ h09YZ _
  have : (affineIndEtaleGamma B T).Faithful := (affineIndEtaleGamma_fullyFaithful B T).faithful
  exact (((affineIndEtaleGamma_fullyFaithful B S).comp
    (.ofFullyFaithful (indEtalePushout (B.inclusion.map f).appTop))).ofIso
      (affineIndEtaleGammaBaseChangeIso B T S f).symm).ofCompFaithful.unop.ofIso
        (affineIndEtaleBaseChange B f).opUnopIso

include h04DZ h09YZ in
private lemma affineIndEtaleBaseChange_essSurj
    [IsAffine S.obj] [IsAffine T.obj]
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f)) :
    (affineIndEtaleBaseChange B f).EssSurj := by
  classical
  have : UniversalHomeomorphism (Spec.map (B.inclusion.map f).appTop) :=
    universalHomeomorphism_spec_appTop B T S f hIntegral hInjective hSurjective
  let G := indEtalePushout (B.inclusion.map f).appTop
  have : G.IsEquivalence := indEtalePushout_isEquivalence h04DZ h09YZ _
  have : (affineIndEtaleGamma B T).Full := (affineIndEtaleGamma_fullyFaithful B T).full
  have : (affineIndEtaleGamma B T).Faithful := (affineIndEtaleGamma_fullyFaithful B T).faithful
  constructor
  intro V
  let C := G.objPreimage ((affineIndEtaleGamma B T).obj (Opposite.op V))
  let e := G.objObjPreimageIso ((affineIndEtaleGamma B T).obj (Opposite.op V))
  let μ := max S.obj.size (max T.obj.size V.obj.obj.left.obj.size)
  have hμ : Cardinal.aleph0 ≤ μ := S.obj.aleph0_le_size.trans (le_max_left _ _)
  have hμlt : μ < B.cutoff := max_lt S.property (max_lt T.property V.obj.obj.left.property)
  have hA : Cardinal.mk Γ(S.obj, ⊤) ≤ μ :=
    (S.obj.mk_sections_le_size ⟨⊤, isAffineOpen_top S.obj⟩).trans (le_max_left _ _)
  have hD : Cardinal.mk Γ(T.obj, ⊤) ≤ μ :=
    (T.obj.mk_sections_le_size ⟨⊤, isAffineOpen_top T.obj⟩).trans
      ((le_max_left _ _).trans (le_max_right _ _))
  have hC : Cardinal.mk ((Under.pushout (B.inclusion.map f).appTop).obj C.obj).right ≤ μ := by
    have hc := Cardinal.mk_congr
      ((Under.forget Γ(T.obj, ⊤)).mapIso
        ((CommRingCat.etale.underObj (X := Γ(T.obj, ⊤))).ind.ι.mapIso
          e)).commRingCatIsoToRingEquiv.toEquiv
    change Cardinal.mk ((Under.pushout (B.inclusion.map f).appTop).obj C.obj).right =
      Cardinal.mk Γ(V.obj.obj.left.obj, ⊤) at hc
    rw [hc]
    exact (V.obj.obj.left.obj.mk_sections_le_size ⟨⊤, isAffineOpen_top _⟩).trans
      ((le_max_right _ _).trans (le_max_right _ _))
  have hsize : (Spec C.obj.right).size < B.cutoff := by
    rw [Scheme.size_Spec]
    exact max_lt B.aleph0_lt_cutoff
      ((mk_indEtaleUnder_le (B.inclusion.map f).appTop C
        (pushout_map_injective_of_faithful _ C) μ hμ hA hD hC).trans_lt
        (B.cutoff_isStrongPrelimit hμlt))
  obtain ⟨U, ⟨eU⟩⟩ := affineIndEtaleGamma_exists_preimage B S C hsize
  let ee : (affineIndEtaleGamma B T).obj ((affineIndEtaleBaseChange B f).op.obj U) ≅
      (affineIndEtaleGamma B T).obj (Opposite.op V) :=
    (affineIndEtaleGammaBaseChangeIso B T S f).app U ≪≫ G.mapIso eU ≪≫ e
  exact ⟨U.unop, ⟨((affineIndEtaleGamma B T).preimageIso ee).unop.symm⟩⟩

include h04DZ h09YZ in
private lemma affineIndEtaleBaseChange_isEquivalence
    [IsAffine S.obj] [IsAffine T.obj]
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f)) :
    (affineIndEtaleBaseChange B f).IsEquivalence where
  faithful := (affineIndEtaleBaseChange_fullyFaithful h04DZ h09YZ B T S f
    hIntegral hInjective hSurjective).faithful
  full := (affineIndEtaleBaseChange_fullyFaithful h04DZ h09YZ B T S f
    hIntegral hInjective hSurjective).full
  essSurj := affineIndEtaleBaseChange_essSurj h04DZ h09YZ B T S f
    hIntegral hInjective hSurjective

private lemma finite_affine_proetaleCover_iff
    {X : Scheme.{u}} (E : PreZeroHypercover.{u + 1} X)
    [IsAffine X] [∀ i, IsAffine (E.X i)] [Finite E.I₀]
    (hE : ∀ i, WeaklyEtale (E.f i)) :
    E.presieve₀ ∈ Scheme.proetalePrecoverage X ↔
      ∀ x, ∃ i, x ∈ Set.range (E.f i) := by
  refine ⟨fun h ↦ ((Scheme.presieve₀_mem_precoverage_iff E).mp h.2).1, fun h ↦ ?_⟩
  have hjs : Scheme.JointlySurjective
      (Scheme.precoverage (@WeaklyEtale : MorphismProperty Scheme.{u})) :=
    Scheme.instJointlySurjectivePrecoverage
  let U : X.Cover (Scheme.precoverage @WeaklyEtale) :=
    ⟨E, (Scheme.presieve₀_mem_precoverage_iff E).mpr ⟨h, hE⟩⟩
  have : ∀ i, QuasiCompact (U.f i) := fun i ↦ quasiCompact_of_compactSpace _
  have : Finite U.I₀ := inferInstanceAs (Finite E.I₀)
  exact ⟨Scheme.presieve₀_mem_qcPrecoverage_iff.mpr
    (QuasiCompactCover.of_finite (𝒰 := U)), U.mem₀⟩

private lemma affineIndEtaleCovering_iff (U : AffineIndEtaleProetale B S)
    (E : PreZeroHypercover.{u + 1} U) :
    AffineIndEtaleProetale.IsCovering B S ⟨U, E⟩ ↔
      Finite E.I₀ ∧ Cardinal.mk E.I₀ ≤ B.coveringBound ∧
      ∀ x : U.obj.obj.left.obj,
        ∃ i, x ∈ Set.range (B.inclusion.map (E.f i).hom.hom.left) := by
  let F := AffineIndEtaleProetale.inclusion B S ⋙ SmallProetale.toScheme B S.obj S.property
  have : IsAffine (F.obj U) := U.property.1
  have : ∀ i, IsAffine ((E.map F).X i) := fun i ↦ (E.X i).property.1
  have hwe (i : E.I₀) : WeaklyEtale ((E.map F).f i) := by
    have : WeaklyEtale (B.inclusion.map U.obj.obj.hom) := U.obj.property
    have hc : WeaklyEtale ((E.map F).f i ≫ B.inclusion.map U.obj.obj.hom) := by
      change WeaklyEtale (B.inclusion.map (E.f i).hom.hom.left ≫ B.inclusion.map U.obj.obj.hom)
      rw [← B.inclusion.map_comp, Over.w]
      exact (E.X i).obj.property
    exact WeaklyEtale.of_comp _ (B.inclusion.map U.obj.obj.hom)
  change ((E.map F).presieve₀ ∈ Scheme.proetalePrecoverage (F.obj U) ∧
      Cardinal.mk E.I₀ ≤ B.coveringBound) ∧ Finite E.I₀ ↔ _
  constructor
  · rintro ⟨⟨h, hb⟩, hf⟩
    have : Finite (E.map F).I₀ := hf
    exact ⟨hf, hb, (finite_affine_proetaleCover_iff (E.map F) hwe).mp h⟩
  · rintro ⟨hf, hb, h⟩
    have : Finite (E.map F).I₀ := hf
    exact ⟨⟨(finite_affine_proetaleCover_iff (E.map F) hwe).mpr h, hb⟩, hf⟩

private lemma pullback_lift_isPullback_of_right
    {C : Type*} [Category C] [HasPullbacks C] {V U T S : C}
    (a : V ⟶ U) (g : U ⟶ S) (g' : V ⟶ S) (f : T ⟶ S)
    (h : a ≫ g = g') :
    IsPullback
      (pullback.lift (pullback.fst g' f ≫ a) (pullback.snd g' f)
        (by rw [Category.assoc, h, pullback.condition]))
      (pullback.fst g' f) (pullback.fst g f) a := by
  apply IsPullback.of_right
    (s := ?_) (p := ?_) (t := (IsPullback.of_hasPullback g f).flip)
  · simpa only [pullback.lift_snd, h] using
      (IsPullback.of_hasPullback g' f).flip
  · simp [pullback.lift_fst]

private lemma jointlySurjective_iff_of_isPullback
    {X Y : Scheme.{u}} (f : X ⟶ Y) [Surjective f]
    {I : Type*} {P Q : I → Scheme.{u}}
    (a : ∀ i, P i ⟶ X) (b : ∀ i, Q i ⟶ Y) (c : ∀ i, P i ⟶ Q i)
    (h : ∀ i, IsPullback (c i) (a i) (b i) f) :
    (∀ x : X, ∃ i, x ∈ Set.range (a i)) ↔
      (∀ y : Y, ∃ i, y ∈ Set.range (b i)) := by
  constructor
  · intro hc y
    obtain ⟨x, rfl⟩ := f.surjective y
    obtain ⟨i, p, rfl⟩ := hc x
    refine ⟨i, c i p, ?_⟩
    change (c i ≫ b i) p = (a i ≫ f) p
    exact congrArg (fun g : P i ⟶ Y ↦ g p) (h i).w
  · intro hc x
    obtain ⟨i, q, hq⟩ := hc (f x)
    obtain ⟨p, -, hpx⟩ := Scheme.exists_preimage_of_isPullback (h i) q x hq
    exact ⟨i, p, hpx⟩

private lemma affineIndEtaleBaseChange_covering_iff [IsAffine S.obj] [IsAffine T.obj]
    (hSurjective : Surjective (B.inclusion.map f))
    (U : AffineIndEtaleProetale B S)
    (E : PreZeroHypercover.{u + 1} U) :
    AffineIndEtaleProetale.IsCovering B T
      ⟨(affineIndEtaleBaseChange B f).obj U,
        E.map (affineIndEtaleBaseChange B f)⟩ ↔
      AffineIndEtaleProetale.IsCovering B S ⟨U, E⟩ := by
  let G := affineIndEtaleBaseChange B f
  have hfU : Surjective (B.inclusion.map (pullback.fst U.obj.obj.hom f)) :=
    MorphismProperty.of_isPullback (P := @Surjective)
      ((IsPullback.of_hasPullback U.obj.obj.hom f).map B.inclusion).flip hSurjective
  have hpb (i : E.I₀) : IsPullback
      (B.inclusion.map ((E.map G).f i).hom.hom.left)
      (B.inclusion.map (pullback.fst (E.X i).obj.obj.hom f))
      (B.inclusion.map (pullback.fst U.obj.obj.hom f))
      (B.inclusion.map (E.f i).hom.hom.left) := by
    change IsPullback (B.inclusion.map (pullback.lift _ _ _))
      (B.inclusion.map (pullback.fst (E.X i).obj.obj.hom f))
      (B.inclusion.map (pullback.fst U.obj.obj.hom f))
      (B.inclusion.map (E.f i).hom.hom.left)
    exact (pullback_lift_isPullback_of_right (E.f i).hom.hom.left U.obj.obj.hom
      (E.X i).obj.obj.hom f (Over.w (E.f i).hom.hom)).map B.inclusion
  rw [affineIndEtaleCovering_iff B T (G.obj U) (E.map G),
    affineIndEtaleCovering_iff B S U E]
  exact and_congr Iff.rfl (and_congr Iff.rfl (jointlySurjective_iff_of_isPullback
    (B.inclusion.map (pullback.fst U.obj.obj.hom f))
    (fun i ↦ B.inclusion.map ((E.map G).f i).hom.hom.left)
    (fun i ↦ B.inclusion.map (E.f i).hom.hom.left)
    (fun i ↦ B.inclusion.map (pullback.fst (E.X i).obj.obj.hom f))
    (fun i ↦ (hpb i).flip)))

private lemma coverPreserving_of_precoverage_map
    {C : Type u₁} [Category.{v₁} C]
    {D : Type u₂} [Category.{v₂} D]
    (P : Precoverage C) (Q : Precoverage D) (F : C ⥤ D) [F.IsEquivalence]
    (h : ∀ (X : C) (R : Presieve X), R ∈ P X → Presieve.map F R ∈ Q (F.obj X)) :
    CoverPreserving P.toGrothendieck Q.toGrothendieck F := by
  have hle : P.toGrothendieck ≤ F.restrictedTopology Q.toGrothendieck := by
    rw [Precoverage.toGrothendieck_le_iff_le_toPrecoverage]
    intro X R hR
    rw [GrothendieckTopology.mem_toPrecoverage_iff,
      Functor.mem_restrictedTopology_iff,
      ← Sieve.generate_map_eq_functorPushforward]
    exact Q.generate_mem_toGrothendieck (h X R hR)
  exact ⟨fun {X S} hS ↦ Functor.mem_restrictedTopology_iff.mp (hle X hS)⟩

private lemma jointlySurjective_map_natIso
    {C : Type*} [Category C] (H : C ⥤ Scheme.{u})
    (K : C ⥤ C) (α : K ≅ 𝟭 C) {V : C} (E : PreZeroHypercover V) :
    (∀ x : (H.obj (K.obj V)), ∃ i, x ∈ Set.range (H.map (K.map (E.f i)))) ↔
      (∀ y : (H.obj V), ∃ i, y ∈ Set.range (H.map (E.f i))) := by
  constructor
  · intro h y
    obtain ⟨x, hx⟩ := (H.map (α.hom.app V)).surjective y
    obtain ⟨i, z, hz⟩ := h x
    refine ⟨i, H.map (α.hom.app (E.X i)) z, ?_⟩
    have hp := congrArg (fun t : H.obj (K.obj (E.X i)) ⟶ H.obj V ↦ t z)
      (congrArg (fun t ↦ H.map t) (α.hom.naturality (E.f i)))
    calc
      _ = (H.map (α.hom.app V)) ((H.map (K.map (E.f i))) z) := by
        simpa only [Functor.map_comp, Scheme.Hom.comp_apply, Functor.id_obj,
          Functor.id_map] using hp.symm
      _ = (H.map (α.hom.app V)) x := congrArg _ hz
      _ = y := hx
  · intro h x
    obtain ⟨i, z, hz⟩ := h (H.map (α.hom.app V) x)
    refine ⟨i, H.map (α.inv.app (E.X i)) z, ?_⟩
    have hp := congrArg (fun t : H.obj (E.X i) ⟶ H.obj (K.obj V) ↦ t z)
      (congrArg (fun t ↦ H.map t) (α.inv.naturality (E.f i)))
    calc
      _ = (H.map (α.inv.app V)) ((H.map (E.f i)) z) := by
        simpa [Functor.map_comp, Scheme.Hom.comp_apply] using hp.symm
      _ = (H.map (α.inv.app V)) ((H.map (α.hom.app V)) x) := congrArg _ hz
      _ = x := by
        rw [← Scheme.Hom.comp_apply, ← H.map_comp, Iso.hom_inv_id_app, H.map_id]
        rfl

private lemma affineIndEtaleBaseChange_inverse_precoverage_map
    [IsAffine S.obj] [IsAffine T.obj]
    [(affineIndEtaleBaseChange B f).IsEquivalence]
    (hSurjective : Surjective (B.inclusion.map f))
    (V : AffineIndEtaleProetale B T) (R : Presieve V)
    (hR : R ∈ AffineIndEtaleProetale.precoverage B T V) :
    Presieve.map (affineIndEtaleBaseChange B f).asEquivalence.inverse R ∈
      AffineIndEtaleProetale.precoverage B S
        ((affineIndEtaleBaseChange B f).asEquivalence.inverse.obj V) := by
  let G := affineIndEtaleBaseChange B f
  let e := G.asEquivalence
  let H := AffineIndEtaleProetale.inclusion B T ⋙
    SmallProetale.toScheme B T.obj T.property
  obtain ⟨E, rfl, hE⟩ := hR
  let E' := E.map e.inverse
  have hcover : AffineIndEtaleProetale.IsCovering B T
      ⟨G.obj (e.inverse.obj V), E'.map G⟩ := by
    rw [affineIndEtaleCovering_iff B T (G.obj (e.inverse.obj V)) (E'.map G)]
    obtain ⟨hfinite, hbound, hs⟩ := (affineIndEtaleCovering_iff B T V E).mp hE
    exact ⟨hfinite, hbound,
      (jointlySurjective_map_natIso H (e.inverse ⋙ e.functor) e.counitIso E).2 hs⟩
  exact ⟨E', (PreZeroHypercover.presieve₀_map (F := e.inverse) E).symm,
    (affineIndEtaleBaseChange_covering_iff B T S f hSurjective (e.inverse.obj V) E').mp hcover⟩

include h04DZ h09YZ in
private lemma affineIndEtaleBaseChange_isCocontinuous
    [IsAffine S.obj] [IsAffine T.obj]
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f)) :
    (affineIndEtaleBaseChange B f).IsCocontinuous
      (AffineIndEtaleProetale.topology B S)
      (AffineIndEtaleProetale.topology B T) := by
  let G := affineIndEtaleBaseChange B f
  have : G.IsEquivalence := affineIndEtaleBaseChange_isEquivalence h04DZ h09YZ B T S f
    hIntegral hInjective hSurjective
  let e := G.asEquivalence
  have hcov : CoverPreserving (AffineIndEtaleProetale.topology B T)
      (AffineIndEtaleProetale.topology B S) e.inverse :=
    coverPreserving_of_precoverage_map
      (AffineIndEtaleProetale.precoverage B T)
      (AffineIndEtaleProetale.precoverage B S) e.inverse
      (affineIndEtaleBaseChange_inverse_precoverage_map B T S f hSurjective)
  exact (e.toAdjunction.isCocontinuous_iff_coverPreserving
    (AffineIndEtaleProetale.topology B S)
    (AffineIndEtaleProetale.topology B T)).2 hcov

private lemma affineIndEtaleBaseChange_sheafEquivalence_of_isCocontinuous
    [IsAffine S.obj] [IsAffine T.obj]
    [(affineIndEtaleBaseChange B f).IsContinuous
      (AffineIndEtaleProetale.topology B S) (AffineIndEtaleProetale.topology B T)]
    [(affineIndEtaleBaseChange B f).IsCocontinuous
      (AffineIndEtaleProetale.topology B S) (AffineIndEtaleProetale.topology B T)]
    [(affineIndEtaleBaseChange B f).IsEquivalence] :
    ((affineIndEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
      (AffineIndEtaleProetale.topology B S)
      (AffineIndEtaleProetale.topology B T)).IsEquivalence := by
  let G := affineIndEtaleBaseChange B f
  let J := AffineIndEtaleProetale.topology B S
  let K := AffineIndEtaleProetale.topology B T
  let e := G.asEquivalence
  have : e.functor.IsCocontinuous J K := inferInstanceAs (G.IsCocontinuous J K)
  have : e.inverse.IsCocontinuous K J :=
    (e.symm.toAdjunction.isCocontinuous_iff_coverPreserving K J).2
      (CoverPreserving.of_isContinuous G J K)
  have : e.inverse.IsDenseSubsite K J :=
    e.isDenseSubsite_inverse_of_isCocontinuous J K
  change (e.sheafCongr J K (Type (u + 1))).inverse.IsEquivalence
  infer_instance

private lemma smallProetalePushforward_isEquivalence_of_app
    [IsAffine S.obj] [IsAffine T.obj]
    [(affineIndEtaleBaseChange B f).IsContinuous
      (AffineIndEtaleProetale.topology B S) (AffineIndEtaleProetale.topology B T)]
    [((affineIndEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
      (AffineIndEtaleProetale.topology B S)
      (AffineIndEtaleProetale.topology B T)).IsEquivalence] :
    (smallProetaleMorphism B T S f).pushforward.IsEquivalence := by
  let F := smallProetaleBaseChange B T S f
  let G := affineIndEtaleBaseChange B f
  let iS := AffineIndEtaleProetale.inclusion B S
  let iT := AffineIndEtaleProetale.inclusion B T
  let JS := SmallProetale.topology B S.obj S.property
  let JT := SmallProetale.topology B T.obj T.property
  let KS := AffineIndEtaleProetale.topology B S
  let KT := AffineIndEtaleProetale.topology B T
  have : F.IsContinuous JS JT :=
    (smallProetaleBaseChange_isMorphismOfSites B T S f).toIsContinuous
  have : (iS ⋙ F).IsContinuous KS JT := Functor.isContinuous_comp iS F KS JS JT
  let e : G ⋙ iT ≅ iS ⋙ F := Iso.refl _
  have : (iS.sheafPushforwardContinuous (Type (u + 1)) KS JS).IsEquivalence :=
    AffineIndEtaleProetale.isEquivalence_restriction.{u, u + 1} B S
  have : (iT.sheafPushforwardContinuous (Type (u + 1)) KT JT).IsEquivalence :=
    AffineIndEtaleProetale.isEquivalence_restriction.{u, u + 1} B T
  let α := (Functor.sheafPushforwardContinuousComp iS F (Type (u + 1)) KS JS JT) ≪≫
    (Functor.sheafPushforwardContinuousComp' e (Type (u + 1)) KS KT JT).symm
  have : ((F.sheafPushforwardContinuous (Type (u + 1)) JS JT) ⋙
      iS.sheafPushforwardContinuous (Type (u + 1)) KS JS).IsEquivalence :=
    Functor.isEquivalence_of_iso α.symm
  exact Functor.isEquivalence_of_comp_right
    (F.sheafPushforwardContinuous (Type (u + 1)) JS JT)
    (iS.sheafPushforwardContinuous (Type (u + 1)) KS JS)

include h04DZ h09YZ in
private lemma smallProetalePushforward_isEquivalence_of_affine
    [IsAffine S.obj] [IsAffine T.obj]
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f)) :
    (smallProetaleMorphism B T S f).pushforward.IsEquivalence := by
  let G := affineIndEtaleBaseChange B f
  have : G.IsEquivalence := affineIndEtaleBaseChange_isEquivalence h04DZ h09YZ B T S f
    hIntegral hInjective hSurjective
  have : G.IsContinuous (AffineIndEtaleProetale.topology B S)
      (AffineIndEtaleProetale.topology B T) :=
    affineIndEtaleBaseChange_isContinuous B f
  have : G.IsCocontinuous (AffineIndEtaleProetale.topology B S)
      (AffineIndEtaleProetale.topology B T) :=
    affineIndEtaleBaseChange_isCocontinuous h04DZ h09YZ B T S f
      hIntegral hInjective hSurjective
  have : (G.sheafPushforwardContinuous (Type (u + 1))
      (AffineIndEtaleProetale.topology B S)
      (AffineIndEtaleProetale.topology B T)).IsEquivalence :=
    affineIndEtaleBaseChange_sheafEquivalence_of_isCocontinuous B T S f
  exact smallProetalePushforward_isEquivalence_of_app B T S f

include h04DZ h09YZ in
private lemma smallProetalePushforward_isEquivalence_over_affine
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f))
    (U : B.Scheme) [IsAffine U.obj] (g : U ⟶ S) :
    (smallProetaleMorphism B (pullback g f) U
      (pullback.fst g f)).pushforward.IsEquivalence := by
  have hpb := (IsPullback.of_hasPullback g f).map B.inclusion
  have : IsAffine (B.inclusion.obj U) := inferInstanceAs (IsAffine U.obj)
  have : IsAffine (pullback g f).obj := IsAffine.of_isPullback hpb
  have hi : IsIntegralHom (B.inclusion.map (pullback.fst g f)) :=
    MorphismProperty.of_isPullback (P := @IsIntegralHom) hpb.flip hIntegral
  have hj : UniversallyInjective (B.inclusion.map (pullback.fst g f)) :=
    MorphismProperty.of_isPullback (P := @UniversallyInjective) hpb.flip hInjective
  have hs : Surjective (B.inclusion.map (pullback.fst g f)) :=
    MorphismProperty.of_isPullback (P := @Surjective) hpb.flip hSurjective
  exact smallProetalePushforward_isEquivalence_of_affine h04DZ h09YZ B (pullback g f) U
    (pullback.fst g f) hi hj hs

private theorem smallProetaleMap_comp_inclusion {T T' : B.Scheme} (f : T' ⟶ T)
    [WeaklyEtale (B.inclusion.map f)] :
    SmallProetale.inclusion B T'.obj T'.property ⋙ Over.map f =
      smallProetaleMap B f ⋙ SmallProetale.inclusion B T.obj T.property := rfl

private lemma smallProetaleMapComm_left_hom_app {T T' : B.Scheme} (f : T' ⟶ T)
    [WeaklyEtale (B.inclusion.map f)] (W : SmallProetale B T'.obj T'.property) :
    (eqToIso (smallProetaleMap_comp_inclusion B f)).hom.app W = 𝟙 _ := rfl

private lemma smallProetaleMapComm_right_hom_app {T T' : B.Scheme} (f : T' ⟶ T)
    (W : SmallProetale B T.obj T.property) :
    (eqToIso (smallProetaleBaseChange_comp_inclusion B T' T f).symm).hom.app W = 𝟙 _ := rfl

private lemma smallProetaleMapComm_left_inv_app {T T' : B.Scheme} (f : T' ⟶ T)
    [WeaklyEtale (B.inclusion.map f)] (W : SmallProetale B T'.obj T'.property) :
    (eqToIso (smallProetaleMap_comp_inclusion B f)).inv.app W = 𝟙 _ := rfl

private lemma smallProetaleMapComm_right_inv_app {T T' : B.Scheme} (f : T' ⟶ T)
    (W : SmallProetale B T.obj T.property) :
    (eqToIso (smallProetaleBaseChange_comp_inclusion B T' T f).symm).inv.app W = 𝟙 _ := rfl

private noncomputable def smallProetaleBaseChangeSquare
    {V U T S : B.Scheme} (k : V ⟶ U) (h : V ⟶ T) (g : U ⟶ S) (f : T ⟶ S)
    [WeaklyEtale (B.inclusion.map g)] [WeaklyEtale (B.inclusion.map h)]
    (hw : k ≫ g = h ≫ f) :
    smallProetaleBaseChange B V U k ⋙ smallProetaleMap B h ⟶
      smallProetaleMap B g ⋙ smallProetaleBaseChange B T S f where
  app W := by
    apply ObjectProperty.homMk
    change Over.mk (pullback.snd W.obj.hom k ≫ h) ⟶
      Over.mk (pullback.snd (W.obj.hom ≫ g) f)
    refine Over.homMk
      (pullback.lift (pullback.fst W.obj.hom k) (pullback.snd W.obj.hom k ≫ h)
        (by change _ ≫ (W.obj.hom ≫ g) = (_ ≫ h) ≫ f
            rw [Category.assoc, ← hw, ← Category.assoc, pullback.condition, Category.assoc])) ?_
    change _ ≫ pullback.snd (W.obj.hom ≫ g) f = pullback.snd W.obj.hom k ≫ h
    exact pullback.lift_snd _ _ _
  naturality W W' a := by
    apply ObjectProperty.hom_ext
    apply Over.OverMorphism.ext
    apply pullback.hom_ext <;>
      simp [smallProetaleMap, smallProetaleBaseChange, pullback.lift_fst, pullback.lift_snd,
        pullback.lift_fst_assoc, pullback.lift_snd_assoc]

/-- A morphism of the small pro-étale site is an isomorphism if its underlying morphism of schemes
is. -/
private lemma isIso_of_isIso_hom_left {T : B.Scheme} {X Y : SmallProetale B T.obj T.property}
    (a : X ⟶ Y) (h : IsIso a.hom.left) : IsIso a :=
  have : IsIso ((SmallProetale.inclusion B T.obj T.property).map a) :=
    @isIso_of_reflects_iso _ _ _ _ _ _ _ (Over.forget T) h _
  isIso_of_reflects_iso a (SmallProetale.inclusion B T.obj T.property)

private lemma smallProetaleBaseChangeSquare_isIso
    {V U T S : B.Scheme} (k : V ⟶ U) (h : V ⟶ T) (g : U ⟶ S) (f : T ⟶ S)
    [WeaklyEtale (B.inclusion.map g)] [WeaklyEtale (B.inclusion.map h)]
    (hp : IsPullback k h g f) :
    IsIso (smallProetaleBaseChangeSquare B k h g f hp.w) := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro W
  have hi : IsIso ((smallProetaleBaseChangeSquare B k h g f hp.w).app W).hom.left := by
    have hp' := ((IsPullback.of_hasPullback W.obj.hom k).flip.paste_horiz hp.flip).flip
    change IsIso (pullback.lift (pullback.fst W.obj.hom k)
      (pullback.snd W.obj.hom k ≫ h) hp'.w)
    have he : pullback.lift (pullback.fst W.obj.hom k)
        (pullback.snd W.obj.hom k ≫ h) hp'.w = hp'.isoPullback.hom := by
      apply pullback.hom_ext
      · exact (pullback.lift_fst _ _ _).trans (IsPullback.isoPullback_hom_fst _).symm
      · exact (pullback.lift_snd _ _ _).trans (IsPullback.isoPullback_hom_snd _).symm
    rw [he]
    infer_instance
  exact isIso_of_isIso_hom_left B _ hi

private lemma smallProetaleMapPullbackAdjunction_eq
    {U S : B.Scheme} (g : U ⟶ S) [WeaklyEtale (B.inclusion.map g)] :
    smallProetaleMapPullbackAdjunction B g =
      (Over.mapPullbackAdj g).restrictFullyFaithful
        (IsWeaklyEtaleOver B U.obj U.property).fullyFaithfulι
        (IsWeaklyEtaleOver B S.obj S.property).fullyFaithfulι
        (eqToIso (smallProetaleMap_comp_inclusion B g))
        (eqToIso (smallProetaleBaseChange_comp_inclusion B U S g).symm) := rfl

private lemma smallProetaleMapPullbackAdjunction_unit
    {U S : B.Scheme} (g : U ⟶ S) [WeaklyEtale (B.inclusion.map g)]
    (W : SmallProetale B U.obj U.property) :
    ((smallProetaleMapPullbackAdjunction B g).unit.app W).hom.left =
      pullback.lift (f := W.obj.hom ≫ g) (g := g) (𝟙 W.obj.left) W.obj.hom (by simp) := by
  change ((SmallProetale.inclusion B U.obj U.property).map
    ((smallProetaleMapPullbackAdjunction B g).unit.app W)).left = _
  rw [smallProetaleMapPullbackAdjunction_eq, Adjunction.map_restrictFullyFaithful_unit_app,
    smallProetaleMapComm_left_hom_app, smallProetaleMapComm_right_hom_app]
  simp [smallProetaleMap, smallProetaleBaseChange]

private lemma smallProetaleMapPullbackAdjunction_counit
    {U S : B.Scheme} (g : U ⟶ S) [WeaklyEtale (B.inclusion.map g)]
    (W : SmallProetale B S.obj S.property) :
    ((smallProetaleMapPullbackAdjunction B g).counit.app W).hom.left =
      pullback.fst W.obj.hom g := by
  change ((SmallProetale.inclusion B S.obj S.property).map
    ((smallProetaleMapPullbackAdjunction B g).counit.app W)).left = _
  rw [smallProetaleMapPullbackAdjunction_eq, Adjunction.map_restrictFullyFaithful_counit_app,
    smallProetaleMapComm_left_inv_app, smallProetaleMapComm_right_inv_app]
  simp [smallProetaleMap, smallProetaleBaseChange]

private lemma smallProetaleBaseChangeSquare_mate_isIso
    {V U T S : B.Scheme} (k : V ⟶ U) (h : V ⟶ T) (g : U ⟶ S) (f : T ⟶ S)
    [WeaklyEtale (B.inclusion.map g)] [WeaklyEtale (B.inclusion.map h)]
    (hw : k ≫ g = h ≫ f) :
    IsIso (mateEquiv (smallProetaleMapPullbackAdjunction B g)
      (smallProetaleMapPullbackAdjunction B h)
      (TwoSquare.mk _ _ _ _ (smallProetaleBaseChangeSquare B k h g f hw))).natTrans := by
  apply (NatTrans.isIso_iff_isIso_app _).mpr
  intro W
  let δ := (mateEquiv (smallProetaleMapPullbackAdjunction B g)
      (smallProetaleMapPullbackAdjunction B h)
      (TwoSquare.mk _ _ _ _ (smallProetaleBaseChangeSquare B k h g f hw))).natTrans.app W
  let e := pullbackLeftPullbackSndIso W.obj.hom g k ≪≫
    pullback.congrHom rfl hw ≪≫ (pullbackLeftPullbackSndIso W.obj.hom f h).symm
  have he : δ.hom.left = e.hom := by
    dsimp only [δ, e]
    rw [mateEquiv_apply]
    apply pullback.hom_ext
    · apply pullback.hom_ext <;>
        simp [smallProetaleMap, smallProetaleBaseChange,
          smallProetaleBaseChangeSquare, smallProetaleMapPullbackAdjunction_unit,
          smallProetaleMapPullbackAdjunction_counit, pullback.lift_fst, pullback.lift_snd,
          pullback.lift_fst_assoc, pullback.lift_snd_assoc]
    · simp [smallProetaleMap, smallProetaleBaseChange,
        smallProetaleBaseChangeSquare, smallProetaleMapPullbackAdjunction_unit,
        smallProetaleMapPullbackAdjunction_counit, pullback.lift_snd]
  have hi : IsIso δ.hom.left := by
    rw [he]
    exact ⟨⟨e.inv, e.hom_inv_id, e.inv_hom_id⟩⟩
  exact isIso_of_isIso_hom_left B _ hi

attribute [local instance] smallProetaleMap_isContinuous

private lemma smallProetale_restrict_of_isPullback
    {V U T S : B.Scheme} (k : V ⟶ U) (h : V ⟶ T) (g : U ⟶ S) (f : T ⟶ S)
    [WeaklyEtale (B.inclusion.map g)] [WeaklyEtale (B.inclusion.map h)]
    (hp : IsPullback k h g f) :
    ((smallProetaleMorphism B V U k).pushforward.IsEquivalence →
      (∀ X, IsIso (((smallProetaleMap B g).sheafPushforwardContinuous (Type (u + 1))
        (SmallProetale.topology B U.obj U.property)
        (SmallProetale.topology B S.obj S.property)).map
          ((smallProetaleMorphism B T S f).adj.unit.app X))) ∧
      (∀ Y, IsIso (((smallProetaleMap B h).sheafPushforwardContinuous (Type (u + 1))
        (SmallProetale.topology B V.obj V.property)
        (SmallProetale.topology B T.obj T.property)).map
          ((smallProetaleMorphism B T S f).adj.counit.app Y)))) ∧
    (IsIso (smallProetaleMorphism B V U k).adj.counit →
      ∀ Y, IsIso (((smallProetaleMap B h).sheafPushforwardContinuous (Type (u + 1))
        (SmallProetale.topology B V.obj V.property)
        (SmallProetale.topology B T.obj T.property)).map
          ((smallProetaleMorphism B T S f).adj.counit.app Y))) := by
  let JU := SmallProetale.topology B U.obj U.property
  let JV := SmallProetale.topology B V.obj V.property
  let JS := SmallProetale.topology B S.obj S.property
  let JT := SmallProetale.topology B T.obj T.property
  let α := smallProetaleBaseChangeSquare B k h g f hp.w
  have : IsIso α := smallProetaleBaseChangeSquare_isIso B k h g f hp
  let a := smallProetaleMapPullbackAdjunction B g
  let b := smallProetaleMapPullbackAdjunction B h
  let σ := sheafSquare (A := Type (u + 1)) JU JS JV JT α
  have : IsIso σ := sheafSquare_isIso JU JS JV JT α
  let τ := (mateEquiv (b.sheafPushforwardContinuous JV JT)
    (a.sheafPushforwardContinuous JU JS) (TwoSquare.mk _ _ _ _ σ)).natTrans
  have : IsIso τ := by
    dsimp only [τ, σ]
    rw [sheafSquare_mate]
    have := smallProetaleBaseChangeSquare_mate_isIso B k h g f hp.w
    exact sheafSquare_isIso JS JT JU JV _
  let γ := asIso τ
  have hmate : IsIso (((mateEquiv (b.sheafPushforwardContinuous JV JT)
      (a.sheafPushforwardContinuous JU JS)).symm
        (TwoSquare.mk _ _ _ _ γ.hom)).natTrans) := by
    change IsIso (((mateEquiv (b.sheafPushforwardContinuous JV JT)
      (a.sheafPushforwardContinuous JU JS)).symm
        ((mateEquiv (b.sheafPushforwardContinuous JV JT)
          (a.sheafPushforwardContinuous JU JS)) (TwoSquare.mk _ _ _ _ σ))).natTrans)
    rw [Equiv.symm_apply_apply]
    exact inferInstanceAs (IsIso σ)
  exact ⟨fun _ ↦ isIso_local_unit_counit (smallProetaleMorphism B T S f).adj
      (smallProetaleMorphism B V U k).adj
      (a.sheafPushforwardContinuous JU JS) (b.sheafPushforwardContinuous JV JT) γ hmate,
    fun _ ↦ isIso_local_counit (smallProetaleMorphism B T S f).adj
      (smallProetaleMorphism B V U k).adj
      (a.sheafPushforwardContinuous JU JS) (b.sheafPushforwardContinuous JV JT) γ hmate⟩

private lemma smallProetale_coversTop {I : Type w} (U : I → B.Scheme)
    (g : ∀ i, U i ⟶ S) [∀ i, WeaklyEtale (B.inclusion.map (g i))]
    (hg : Presieve.ofArrows (fun i ↦ (U i).obj) (fun i ↦ B.inclusion.map (g i)) ∈
      Scheme.proetalePrecoverage S.obj) :
    (SmallProetale.topology B S.obj S.property).CoversTop
      (fun i ↦ (⟨Over.mk (g i),
        inferInstanceAs (WeaklyEtale (B.inclusion.map (g i)))⟩ :
          SmallProetale B S.obj S.property)) := by
  let Z : SmallProetale B S.obj S.property := ⟨Over.mk (𝟙 S), by
    change WeaklyEtale (B.inclusion.map (𝟙 S))
    rw [CategoryTheory.Functor.map_id]
    infer_instance⟩
  have hz : IsTerminal Z := IsTerminal.ofUniqueHom
    (fun W ↦ ObjectProperty.homMk (Over.homMk W.obj.hom (by
      change W.obj.hom ≫ 𝟙 S = W.obj.hom
      simp))) (fun _ _ ↦ ObjectProperty.hom_ext _ (Over.mkIdTerminal.hom_ext _ _))
  apply ((SmallProetale.topology B S.obj S.property).coversTop_iff_of_isTerminal Z hz _).mpr
  let R := Sieve.ofArrows U g
  have hr : R ∈ B.topology S := by
    apply Precoverage.generate_mem_toGrothendieck
    rw [B.precoverage_eq_comap, Precoverage.mem_comap_iff, Presieve.map_ofArrows]
    exact hg
  let Q := (Sieve.overEquiv Z.obj).symm R
  have hq : Q ∈ BigProetaleOver.topology B S.obj S.property Z.obj :=
    B.topology.overEquiv_symm_mem_over _ _ hr
  let i := SmallProetale.inclusion B S.obj S.property
  let e : smallProetaleToBigProetaleFunctor B S S (𝟙 S) ≅ i :=
    Functor.isoWhiskerLeft _ (Over.mapId S) ≪≫ Functor.rightUnitor _
  have : i.IsCocontinuous (SmallProetale.topology B S.obj S.property)
      (BigProetaleOver.topology B S.obj S.property) := Functor.IsCocontinuous.of_iso e
  apply (SmallProetale.topology B S.obj S.property).superset_covering _ (i.cover_lift _ _ hq)
  intro W a ha
  change R a.hom.left at ha
  obtain ⟨D, b, _, ⟨j⟩, hb⟩ := ha
  refine ⟨j, ⟨ObjectProperty.homMk (Over.homMk b ?_)⟩⟩
  apply hb.trans
  have hw := Over.w a.hom
  change a.hom.left ≫ 𝟙 S = W.obj.hom at hw
  exact (CategoryTheory.Category.comp_id a.hom.left).symm.trans hw

private lemma smallProetale_restrictions_jointly_reflect_isomorphisms
    {I : Type w} (U : I → B.Scheme) (g : ∀ i, U i ⟶ S)
    [∀ i, WeaklyEtale (B.inclusion.map (g i))]
    (hg : Presieve.ofArrows (fun i ↦ (U i).obj) (fun i ↦ B.inclusion.map (g i)) ∈
      Scheme.proetalePrecoverage S.obj)
    {F G : Sheaf (SmallProetale.topology B S.obj S.property) (Type (u + 1))}
    (α : F ⟶ G)
    (hα : ∀ i, IsIso (((smallProetaleMap B (g i)).sheafPushforwardContinuous
      (Type (u + 1)) (SmallProetale.topology B (U i).obj (U i).property)
      (SmallProetale.topology B S.obj S.property)).map α)) : IsIso α := by
  apply Sheaf.isIso_of_coversTop (smallProetale_coversTop B S U g hg)
  intro i
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro W
  let q := W.unop.hom.hom.left
  have hq : WeaklyEtale (B.inclusion.map q) := by
    have : WeaklyEtale (B.inclusion.map q ≫ B.inclusion.map (g i)) := by
      rw [← CategoryTheory.Functor.map_comp,
        show q ≫ g i = W.unop.left.obj.hom from Over.w W.unop.hom.hom]
      exact W.unop.left.property
    exact WeaklyEtale.of_comp _ (B.inclusion.map (g i))
  let V : SmallProetale B (U i).obj (U i).property := ⟨Over.mk q, hq⟩
  let e : (smallProetaleMap B (g i)).obj V ≅ W.unop.left :=
    (IsWeaklyEtaleOver B S.obj S.property).isoMk
      (Over.isoMk (Iso.refl _) (by
        simpa [q, V, smallProetaleMap] using (Over.w W.unop.hom.hom).symm))
  have hi : IsIso (α.hom.app (Opposite.op ((smallProetaleMap B (g i)).obj V))) :=
    (NatTrans.isIso_iff_isIso_app
      (((smallProetaleMap B (g i)).sheafPushforwardContinuous
        (Type (u + 1)) (SmallProetale.topology B (U i).obj (U i).property)
        (SmallProetale.topology B S.obj S.property)).map α).hom).mp
          (by
            have := hα i
            infer_instance) (Opposite.op V)
  change IsIso (α.hom.app (Opposite.op W.unop.left))
  have hc : IsIso (α.hom.app (Opposite.op W.unop.left) ≫ G.obj.map e.hom.op) := by
    rw [← α.hom.naturality]
    infer_instance
  exact IsIso.of_isIso_comp_right _ (G.obj.map e.hom.op)

private lemma proetale_cover_of_open {X : Scheme.{u}} {I : Type w}
    (U : I → Scheme.{u}) (g : ∀ i, U i ⟶ X) [∀ i, IsOpenImmersion (g i)]
    (hg : ∀ x, ∃ i, x ∈ Set.range (g i)) :
    Presieve.ofArrows U g ∈ Scheme.proetalePrecoverage X := by
  apply Scheme.etalePrecoverage_le_proetalePrecoverage
  exact (Scheme.presieve₀_mem_precoverage_iff (P := @Etale) ⟨I, U, g⟩).mpr
    ⟨hg, fun i ↦ inferInstance⟩

/-- An affine open of a scheme in a chosen big pro-étale site, as an object of that site. -/
def affineOpenObj (U : S.obj.affineOpens) : B.Scheme :=
  ⟨U.1.toScheme, (Scheme.size_coe_opens_le S.obj U.1).trans_lt S.property⟩

/-- The open immersion of an affine open into the ambient object of the chosen big site. -/
def affineOpenMap (U : S.obj.affineOpens) : affineOpenObj B S U ⟶ S :=
  ObjectProperty.homMk U.1.ι

/-- The scheme underlying an affine open is affine. -/
theorem affineOpenObj_isAffine (U : S.obj.affineOpens) :
    IsAffine (affineOpenObj B S U).obj := U.2

/-- The affine opens of the ambient object of the chosen big site cover it. -/
theorem exists_mem_range_affineOpenMap (x : S.obj) :
    ∃ U, x ∈ Set.range (B.inclusion.map (affineOpenMap B S U)) := by
  obtain ⟨W, hW, hx, _⟩ := exists_isAffineOpen_mem_and_subset
    (X := S.obj) (U := ⊤) (x := x) (by trivial)
  exact ⟨⟨W, hW⟩, ⟨x, hx⟩, rfl⟩

/-- The open immersion of an affine open is an open immersion of underlying schemes. -/
private lemma isOpenImmersion_map_affineOpenMap (U : S.obj.affineOpens) :
    IsOpenImmersion (B.inclusion.map (affineOpenMap B S U)) :=
  inferInstanceAs (IsOpenImmersion U.1.ι)

/-- Base change of an affine open immersion along `f` is an open immersion. -/
private lemma isOpenImmersion_map_pullback_snd_affineOpenMap (U : S.obj.affineOpens) :
    IsOpenImmersion (B.inclusion.map (pullback.snd (affineOpenMap B S U) f)) :=
  have := isOpenImmersion_map_affineOpenMap B S U
  MorphismProperty.of_isPullback (P := @IsOpenImmersion)
    ((IsPullback.of_hasPullback (affineOpenMap B S U) f).map B.inclusion)
    (isOpenImmersion_map_affineOpenMap B S U)

/-- The counit of a small pro-étale morphism is an isomorphism if it is so after base change to
every affine open of the target. -/
theorem smallProetaleMorphism_counit_isIso_of_affineOpen
    (hlocal : ∀ U : S.obj.affineOpens,
      IsIso (smallProetaleMorphism B
        (pullback (affineOpenMap B S U) f) (affineOpenObj B S U)
        (pullback.fst (affineOpenMap B S U) f)).adj.counit) :
    IsIso (smallProetaleMorphism B T S f).adj.counit := by
  classical
  let g := affineOpenMap B S
  let V := fun i ↦ pullback (g i) f
  let k := fun i ↦ pullback.fst (g i) f
  let h := fun i ↦ pullback.snd (g i) f
  have hpb (i : S.obj.affineOpens) : IsPullback (k i) (h i) (g i) f :=
    IsPullback.of_hasPullback (g i) f
  have hpb' (i : S.obj.affineOpens) := (hpb i).map B.inclusion
  have := isOpenImmersion_map_affineOpenMap B S
  have := isOpenImmersion_map_pullback_snd_affineOpenMap B T S f
  have hcS : ∀ x : S.obj, ∃ i, x ∈ Set.range (B.inclusion.map (g i)) :=
    exists_mem_range_affineOpenMap B S
  have hcT : ∀ x : T.obj, ∃ i, x ∈ Set.range (B.inclusion.map (h i)) := by
    intro x
    obtain ⟨i, q, hq⟩ := hcS ((B.inclusion.map f) x)
    obtain ⟨p, -, hpx⟩ := Scheme.exists_preimage_of_isPullback (hpb' i) q x hq
    exact ⟨i, p, hpx⟩
  have hh := proetale_cover_of_open (fun i ↦ (V i).obj)
    (fun i ↦ B.inclusion.map (h i)) hcT
  have hi (i : S.obj.affineOpens) :=
    (smallProetale_restrict_of_isPullback B (k i) (h i) (g i) f (hpb i)).2 (hlocal i)
  exact (NatTrans.isIso_iff_isIso_app _).mpr fun X ↦
    smallProetale_restrictions_jointly_reflect_isomorphisms B T V h hh
      ((smallProetaleMorphism B T S f).adj.counit.app X) (fun i ↦ hi i X)

include h04DZ h09YZ in
private lemma smallProetalePushforward_isEquivalence_over_affineOpen
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f))
    (U : S.obj.affineOpens) :
    (smallProetaleMorphism B
      (pullback (affineOpenMap B S U) f) (affineOpenObj B S U)
      (pullback.fst (affineOpenMap B S U) f)).pushforward.IsEquivalence := by
  have := affineOpenObj_isAffine B S U
  exact smallProetalePushforward_isEquivalence_over_affine h04DZ h09YZ B T S f
    hIntegral hInjective hSurjective (affineOpenObj B S U) (affineOpenMap B S U)

include h04DZ h09YZ in
/-- **Topological invariance of the small pro-étale topos, direct image.** For an integral,
universally injective and surjective morphism `f : T ⟶ S` in a chosen big pro-étale site, the
direct image of the induced morphism of small pro-étale topoi is an equivalence.

This is the direct-image half of Stacks Project, Tag 09AB, with the two inputs that this library
does not have carried as explicit hypotheses: essential surjectivity of base change on small
étale sites, which is the remaining content of Stacks Project, Tag 04DZ, and
`AlgebraicGeometry.IntegralHasFinitePresentationLimit`, which is Stacks Project, Tag 09YZ over a
quasi-compact quasi-separated base and is what Stacks Project, Tag 05YU still needs. -/
@[stacks 09AB "direct image, assuming essential surjectivity of etale pullback (the content of
Stacks 04DZ) and Stacks 09YZ over a qcqs base"]
theorem smallProetalePushforward_isEquivalence
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f)) :
    (smallProetaleMorphism B T S f).pushforward.IsEquivalence := by
  classical
  let U := affineOpenObj B S
  let g := affineOpenMap B S
  let V := fun i ↦ pullback (g i) f
  let k := fun i ↦ pullback.fst (g i) f
  let h := fun i ↦ pullback.snd (g i) f
  have hpb (i : S.obj.affineOpens) : IsPullback (k i) (h i) (g i) f :=
    IsPullback.of_hasPullback (g i) f
  have := isOpenImmersion_map_affineOpenMap B S
  have := isOpenImmersion_map_pullback_snd_affineOpenMap B T S f
  have hcS : ∀ x : S.obj, ∃ i, x ∈ Set.range (B.inclusion.map (g i)) :=
    exists_mem_range_affineOpenMap B S
  have hg := proetale_cover_of_open (fun i ↦ (U i).obj)
    (fun i ↦ B.inclusion.map (g i)) hcS
  have (i : S.obj.affineOpens) :
      (smallProetaleMorphism B (V i) (U i) (k i)).pushforward.IsEquivalence :=
    smallProetalePushforward_isEquivalence_over_affineOpen h04DZ h09YZ B T S f
      hIntegral hInjective hSurjective i
  have hi (i : S.obj.affineOpens) :=
    (smallProetale_restrict_of_isPullback B (k i) (h i) (g i) f (hpb i)).1 inferInstance
  have : IsIso (smallProetaleMorphism B T S f).adj.unit :=
    (NatTrans.isIso_iff_isIso_app _).mpr fun X ↦
      smallProetale_restrictions_jointly_reflect_isomorphisms B S U g hg
        ((smallProetaleMorphism B T S f).adj.unit.app X) (fun i ↦ (hi i).1 X)
  have : IsIso (smallProetaleMorphism B T S f).adj.counit :=
    smallProetaleMorphism_counit_isIso_of_affineOpen B T S f fun i ↦ by
      have := smallProetalePushforward_isEquivalence_over_affineOpen h04DZ h09YZ B T S f
        hIntegral hInjective hSurjective i
      infer_instance
  exact (smallProetaleMorphism B T S f).adj.toEquivalence.isEquivalence_inverse

include h04DZ h09YZ in
/-- **Topological invariance of the small pro-étale topos, inverse image.** For an integral,
universally injective and surjective morphism `f : T ⟶ S` in a chosen big pro-étale site, the
inverse image of the induced morphism of small pro-étale topoi is an equivalence.

Together with `AlgebraicGeometry.ProEtale.smallProetalePushforward_isEquivalence` and
`CategoryTheory.Adjunction.toEquivalence` of the adjunction `f⁻¹ ⊣ f_*`, this is Stacks Project,
Tag 09AB; its two hypotheses are those of the direct-image half. -/
@[stacks 09AB "inverse image, assuming essential surjectivity of etale pullback (the content of
Stacks 04DZ) and Stacks 09YZ over a qcqs base"]
theorem smallProetaleInverseImage_isEquivalence
    (hIntegral : IsIntegralHom (B.inclusion.map f))
    (hInjective : UniversallyInjective (B.inclusion.map f))
    (hSurjective : Surjective (B.inclusion.map f)) :
    (smallProetaleMorphism B T S f).inverseImage.IsEquivalence :=
  have : (smallProetaleMorphism B T S f).pushforward.IsEquivalence :=
    smallProetalePushforward_isEquivalence h04DZ h09YZ B T S f
      hIntegral hInjective hSurjective
  smallProetaleInverseImage_isEquivalence_of_pushforward B T S f

end AlgebraicGeometry.ProEtale

end
