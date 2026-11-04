module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.EtaleLocalBaseChange
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocality
import all StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocalityRightSquareCube

/-!
# Stacks 0EZR, part (1): the étale-local criterion for the set-valued base change map

Consider a cartesian square of schemes

```
X <--h-- Y
|f       |e
S <--g-- T
```

and let `{Uᵢ → X}` be an étale covering such that each `Uᵢ → S` factors as `Uᵢ → Vᵢ → S` with
`Vᵢ → S` étale.  Writing `Yᵢ = Uᵢ ×_X Y` and `Tᵢ = Vᵢ ×_S T`, the induced squares

```
Uᵢ <--hᵢ-- Yᵢ
|fᵢ        |eᵢ
Vᵢ <--gᵢ-- Tᵢ
```

are again cartesian.  This file proves the first part of Stacks 0EZR for sheaves of sets: the
base change map `Stacks.EtaleCohomology.smallEtaleSetsBaseChange` of the outer square, built in
`StacksFrontier/AlgebraicGeometry/EtaleCohomology/BaseChangeHigher/OrdinaryLocality.lean` together
with the data `Stacks.EtaleCohomology.EtaleLocalBaseChangeData` and the mate calculus, is an
isomorphism as soon as the base change map of each of the local squares is.  Parts (2) and (3),
the analogues for an object of the unbounded derived category and for the higher direct images,
are not proved here.

## Main results

* `Stacks.EtaleCohomology.isIso_smallEtaleSetsBaseChange_of_isIso_local` — **Stacks 0EZR, part
  (1)**: the base change map of the outer square is an isomorphism as soon as the base change
  map of each local square is.
* `Stacks.EtaleCohomology.baseChange_isIso_of_etale` (private) — the base change map of a
  cartesian square whose two vertical sides are étale is an isomorphism, which is the appeal to
  Sites, Lemma 03EF in the source.

## Implementation notes

The source's argument compares the restriction to `Uᵢ` of the base change map of the outer square
with the base change map of the `i`-th local square through the pasting law for mates: the
rectangle `Uᵢ ⟶ X ⟶ S` obtained by stacking the outer square on the `i`-th upper square is the
one obtained by stacking the `i`-th local square on the `i`-th lower square, because
`Uᵢ → X → S` equals `Uᵢ → Vᵢ → S`.  Two of the four base change maps occurring in that
comparison are invertible for free, being attached to cartesian squares one side of which is
étale.  The comparison of the two composite direct images, `rightSquare`, acts on sections by
the comparison `siteSquare` of the two composite base change functors of sites
(`rightSquare_app`); the pasting identity itself is `rightSquare_cube`, and the invertibility it
yields is assembled by `isIso_map_mate_of_cube`.  Both `rightSquare_app` and `rightSquare_cube`
are the private lemmas of
`StacksFrontier.AlgebraicGeometry.EtaleCohomology.BaseChangeHigher.OrdinaryLocalityRightSquareCube`,
reached here through `import all`.

## References

* [Stacks Project, Tag 0EZR](https://stacks.math.columbia.edu/tag/0EZR)
* [Stacks Project, Tag 03EF](https://stacks.math.columbia.edu/tag/03EF)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme AlgebraicGeometry.Scheme.Etale

universe u v z

namespace Stacks.EtaleCohomology

/-! ### The base change map of a cartesian square with one side étale, concluded

For a cartesian square one side of which is étale, the base change map is invertible.  The
ingredients are in place: `siteSquare` is invertible at the site level because its component is a
comparison of two cartesian squares (`isIso_pullbackLift_of_isPullback`), `rightSquare_app` and
`mate_sheafPushforward_app` carry that invertibility to the mate taken with respect to the
restriction adjunctions, and `isIso_mate_symm_iff` replaces restriction by the inverse image. -/

section EtaleSquareIsIso

/-- Reassociation of a four-fold composite against a known identity for its last three factors,
in term mode.  The goals this is applied to mention `AlgebraicGeometry.Scheme.Etale` through the
objects of their morphisms, where `rw [Category.assoc]` cannot typecheck its motive; here the
category is a variable, so `simp only [Category.assoc]` applies. -/
private lemma comp_four_proj {C : Type*} [Category* C] {A B D E Z : C}
    (a : A ⟶ B) (b : B ⟶ D) (c : D ⟶ E) (d : E ⟶ Z) {p : B ⟶ Z} {q : A ⟶ Z}
    (hb : b ≫ c ≫ d = p) (ha : a ≫ p = q) :
    (a ≫ b ≫ c) ≫ d = q :=
  calc (a ≫ b ≫ c) ≫ d = a ≫ b ≫ c ≫ d := by simp only [Category.assoc]
    _ = a ≫ p := by rw [hb]
    _ = q := ha

/-- The unit of the composition/base-change adjunction of small étale sites, followed by the
projection to the base, is the identity. -/
private lemma composeAdj_unit_left_fst {X S : Scheme.{u}} (j : X ⟶ S) [Etale j]
    (V : X.Etale) :
    ((smallEtaleComposeBaseChangeAdj j).unit.app V).left ≫
      pullback.fst ((smallEtaleCompose j).obj V).hom j = 𝟙 V.left :=
  pullback.lift_fst _ _ _

/-- Equal morphisms of the small étale site have equal underlying morphisms. -/
private lemma etaleOver_left_congr {X : Scheme.{u}} {A B : X.Etale} {m n : A ⟶ B} (q : m = n) :
    m.left = n.left :=
  congrArg (fun k : A ⟶ B => k.left) q

/-- **The site comparison of a cartesian square with one side étale is invertible.**  The mate of
`siteSquare` under the two composition/base-change adjunctions has, on underlying schemes, the
comparison `V ×_X Y ⟶ V ×_S T` of two cartesian squares for its component, which is invertible by
`isIso_pullbackLift_of_isPullback`; the forgetful functor to schemes reflects isomorphisms. -/
private lemma siteMate_isIso {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)
    (sq : IsPullback e h g f) [Etale e] [Etale f] (V : X.Etale) :
    IsIso (((mateEquiv (smallEtaleComposeBaseChangeAdj f)
      (smallEtaleComposeBaseChangeAdj e)).symm (siteSquare e h g f w).hom).app V) := by
  have hw : pullback.fst V.hom h ≫ (V.hom ≫ f) = (pullback.snd V.hom h ≫ e) ≫ g := by
    simp only [Category.assoc, sq.w, ← pullback.condition_assoc]
  have htl : (((mateEquiv (smallEtaleComposeBaseChangeAdj f)
        (smallEtaleComposeBaseChangeAdj e)).symm
        (siteSquare e h g f w).hom).app V).left =
      ((smallEtaleBaseChange h).map
          ((smallEtaleComposeBaseChangeAdj f).unit.app V)).left ≫
        ((siteSquare e h g f w).hom.app ((smallEtaleCompose f).obj V)).left ≫
        pullback.fst (pullback.snd ((smallEtaleCompose f).obj V).hom g) e :=
    (etaleOver_left_congr (mate_symm_app_eq (smallEtaleComposeBaseChangeAdj f)
      (smallEtaleComposeBaseChangeAdj e) (siteSquare e h g f w).hom V)).trans
      (etaleOver_comp₃_left _ _ _)
  have ht : (((mateEquiv (smallEtaleComposeBaseChangeAdj f)
        (smallEtaleComposeBaseChangeAdj e)).symm
        (siteSquare e h g f w).hom).app V).left =
      pullback.lift (pullback.fst V.hom h) (pullback.snd V.hom h ≫ e) hw := by
    refine pullback.hom_ext (Eq.trans ?_ (pullback.lift_fst _ _ _).symm)
      (Eq.trans ?_ (pullback.lift_snd _ _ _).symm)
    · exact (congrArg (fun m => m ≫ pullback.fst ((smallEtaleCompose f).obj V).hom g) htl).trans
        (comp_four_proj _ _ _ _
          (siteSquare_hom_fst e h g f w ((smallEtaleCompose f).obj V))
          ((baseChange_map_projection h ((smallEtaleComposeBaseChangeAdj f).unit.app V)
            (composeAdj_unit_left_fst f V)).trans (Category.comp_id _)))
    · exact MorphismProperty.Over.w _
  have h1 : IsIso (((mateEquiv (smallEtaleComposeBaseChangeAdj f)
      (smallEtaleComposeBaseChangeAdj e)).symm
      (siteSquare e h g f w).hom).app V).left := by
    rw [ht]
    exact isIso_pullbackLift_of_isPullback sq V.hom hw
  have h2 : IsIso ((Scheme.Etale.forget T ⋙ Over.forget T).map
    (((mateEquiv (smallEtaleComposeBaseChangeAdj f)
      (smallEtaleComposeBaseChangeAdj e)).symm
      (siteSquare e h g f w).hom).app V)) := h1
  exact isIso_of_reflects_iso _ (Scheme.Etale.forget T ⋙ Over.forget T)

/-- **The base change map formed with restriction is invertible for a cartesian square with both
vertical sides étale.**  Its components are the images under `F` of the components of the site
mate, by `rightSquare_app` and `mate_sheafPushforward_app`. -/
private lemma restrictionBaseChange_isIso {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)
    (sq : IsPullback e h g f) [Etale e] [Etale f]
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    IsIso ((restrictionBaseChange.{u, v} e h g f w).app F) := by
  rw [← ObjectProperty.isIso_hom_iff, NatTrans.isIso_iff_isIso_app]
  intro V
  have hiso := siteMate_isIso e h g f w sq V.unop
  have hmate : ((restrictionBaseChange.{u, v} e h g f w).app F).hom.app (op V.unop) =
      F.obj.map (((mateEquiv (smallEtaleComposeBaseChangeAdj f)
        (smallEtaleComposeBaseChangeAdj e)).symm
        (siteSquare e h g f w).hom).app V.unop).op :=
    mate_sheafPushforward_app _ _ _ _ (smallEtaleComposeBaseChangeAdj f)
      (smallEtaleComposeBaseChangeAdj e) (siteSquare e h g f w).hom _
      (rightSquare_app.{u, v} e h g f w) F V.unop
  show IsIso (((restrictionBaseChange.{u, v} e h g f w).app F).hom.app (op V.unop))
  rw [hmate]
  exact Functor.map_isIso F.obj _

/-- The base change map of sheaves of sets is the mate of the right square under the two
inverse-image/direct-image adjunctions. -/
private lemma smallEtaleSetsBaseChange_eq {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f) :
    smallEtaleSetsBaseChange.{u, v} e h g f w =
      (mateEquiv (adj.{u, v} e) (adj.{u, v} f)).symm (rightSquare.{u, v} e h g f w).hom :=
  rfl

/-- **The base change map of a cartesian square with both vertical sides étale is invertible.**
This is the appeal to Sites, Lemma 03EF in the proof of Stacks 0EZR: it identifies `g_* F|_{V_i}`
with `g_{i,*} F_i` and `h_* e^{-1} F|_{U_i}` with `h_{i,*} e_i^{-1} F_i`.  Restriction along an
étale morphism and the inverse image along it are both left adjoint to the direct image, so the
two mates of the right square are invertible together. -/
private lemma baseChange_isIso_of_etale {Y T X S : Scheme.{u}}
    (e : Y ⟶ T) (h : Y ⟶ X) (g : T ⟶ S) (f : X ⟶ S) (w : e ≫ g = h ≫ f)
    (sq : IsPullback e h g f) [Etale e] [Etale f]
    (F : Sheaf (smallEtaleTopology T) (Type (max (u + 1) v))) :
    IsIso ((smallEtaleSetsBaseChange.{u, v} e h g f w).app F) := by
  rw [smallEtaleSetsBaseChange_eq.{u, v} e h g f w]
  refine (isIso_mate_symm_iff (adj.{u, v} e) (restrictionAdjunction.{u, v} e)
    (adj.{u, v} f) (restrictionAdjunction.{u, v} f) (rightSquare.{u, v} e h g f w).hom
    (rightSquare.{u, v} e h g f w).hom (Iso.refl _) (Iso.refl _) ?_ F).mpr
    (restrictionBaseChange_isIso e h g f w sq F)
  apply TwoSquare.ext
  intro P
  show (rightSquare.{u, v} e h g f w).hom.app P =
    (push.{u, v} g).map (𝟙 ((push.{u, v} e).obj P)) ≫
      (rightSquare.{u, v} e h g f w).hom.app P
  rw [(push.{u, v} g).map_id, Category.id_comp]

end EtaleSquareIsIso

/-! ### Stacks 0EZR, part (1)

The three mates attached to the three squares other than the outer one are invertible: two of
them because their squares are cartesian with one side étale (`baseChange_isIso_of_etale` and
`restrictionBaseChange_isIso`), and the third because it is the hypothesis of the tag.  By
`isIso_map_mate_of_cube` the restriction to `Uᵢ` of the base change map of the outer square is
then invertible, and invertibility on the small étale site of `X` is local on an étale
covering. -/

section OrdinaryLocal

/-- The mate attached to the `i`-th upper square is invertible: that square is cartesian and both
its vertical sides are étale, `Uᵢ ⟶ X` by hypothesis and `Uᵢ ×_X Y ⟶ Y` by base change. -/
private lemma upperMate_isIso
    (D : EtaleLocalBaseChangeData.{u, z, max (u + 1) v, (max (u + 1) v) + 1}
      (Type (max (u + 1) v))) (i : D.I) [Etale (D.u i)] [Etale (D.toY_i i)] :
    IsIso (((mateEquiv (restrictionAdjunction.{u, v} (D.toY_i i))
      (restrictionAdjunction.{u, v} (D.u i))).symm
      (rightSquare.{u, v} (D.toY_i i) (D.h_i i) D.h (D.u i)
        (D.upper_cartesian i).w.symm).hom).app ((invImage.{u, v} D.e).obj D.F)) := by
  exact restrictionBaseChange_isIso (D.toY_i i) (D.h_i i) D.h (D.u i)
    (D.upper_cartesian i).w.symm (D.upper_cartesian i).flip
    ((invImage.{u, v} D.e).obj D.F)

/-- The mate attached to the `i`-th lower square is invertible: that square is cartesian and both
its vertical sides are étale, `Vᵢ ⟶ S` by hypothesis and `Vᵢ ×_S T ⟶ T` by base change. -/
private lemma lowerMate_isIso
    (D : EtaleLocalBaseChangeData.{u, z, max (u + 1) v, (max (u + 1) v) + 1}
      (Type (max (u + 1) v))) (i : D.I) [Etale (D.v i)] [Etale (D.toT_i i)] :
    IsIso (((mateEquiv (adj.{u, v} (D.toT_i i)) (adj.{u, v} (D.v i))).symm
      (rightSquare.{u, v} (D.toT_i i) (D.g_i i) D.g (D.v i)
        (D.lower_cartesian i).w.symm).hom).app D.F) := by
  rw [← smallEtaleSetsBaseChange_eq.{u, v} (D.toT_i i) (D.g_i i) D.g (D.v i)
    (D.lower_cartesian i).w.symm]
  exact baseChange_isIso_of_etale (D.toT_i i) (D.g_i i) D.g (D.v i)
    (D.lower_cartesian i).w.symm (D.lower_cartesian i).flip D.F

/-- The hypothesis of Stacks 0EZR (1) for the `i`-th local square, read as invertibility of the
mate of the `i`-th local right square. -/
private lemma localMate_isIso
    (D : EtaleLocalBaseChangeData.{u, z, max (u + 1) v, (max (u + 1) v) + 1}
      (Type (max (u + 1) v))) (i : D.I)
    (hlocal : IsIso ((smallEtaleSetsBaseChange.{u, v} (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
      (D.local_cartesian i).w.symm).app
      ((smallEtaleInverseImage.{u, v} (D.toT_i i)).obj D.F))) :
    IsIso (((mateEquiv (adj.{u, v} (D.e_i i)) (adj.{u, v} (D.f_i i))).symm
      (rightSquare.{u, v} (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
        (D.local_cartesian i).w.symm).hom).app
      ((invImage.{u, v} (D.toT_i i)).obj D.F)) := by
  rwa [← smallEtaleSetsBaseChange_eq.{u, v} (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
    (D.local_cartesian i).w.symm]

/-- **The restriction to `Uᵢ` of the base change map of the outer square is invertible.**  Three
of the four mates of the cube of right squares are invertible, so by `isIso_map_mate_of_cube` the
image of the fourth under restriction along `Uᵢ ⟶ X` is invertible as well. -/
private lemma localBaseChange_isIso
    (D : EtaleLocalBaseChangeData.{u, z, max (u + 1) v, (max (u + 1) v) + 1}
      (Type (max (u + 1) v))) (i : D.I) [Etale (D.u i)]
    (hlocal : IsIso ((smallEtaleSetsBaseChange.{u, v} (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
      (D.local_cartesian i).w.symm).app
      ((smallEtaleInverseImage.{u, v} (D.toT_i i)).obj D.F))) :
    IsIso ((restriction.{u, v} (D.u i)).map
      (((mateEquiv (adj.{u, v} D.e) (adj.{u, v} D.f)).symm
        (rightSquare.{u, v} D.e D.h D.g D.f D.cartesian.w.symm).hom).app D.F)) := by
  have : Etale (D.v i) := D.etale_v i
  have : Etale (D.toY_i i) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (D.upper_cartesian i) (inferInstance : Etale (D.u i))
  have : Etale (D.toT_i i) :=
    MorphismProperty.IsStableUnderBaseChange.of_isPullback
      (D.lower_cartesian i) (D.etale_v i)
  have := upperMate_isIso D i
  have := lowerMate_isIso D i
  have := localMate_isIso D i hlocal
  exact isIso_map_mate_of_cube (adj.{u, v} D.e) (adj.{u, v} D.f)
    (restrictionAdjunction.{u, v} (D.toY_i i)) (restrictionAdjunction.{u, v} (D.u i))
    (adj.{u, v} (D.toT_i i)) (adj.{u, v} (D.v i)) (adj.{u, v} (D.e_i i))
    (adj.{u, v} (D.f_i i))
    (rightSquare.{u, v} D.e D.h D.g D.f D.cartesian.w.symm).hom
    (rightSquare.{u, v} (D.toY_i i) (D.h_i i) D.h (D.u i)
      (D.upper_cartesian i).w.symm).hom
    (rightSquare.{u, v} (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
      (D.local_cartesian i).w.symm).hom
    (rightSquare.{u, v} (D.toT_i i) (D.g_i i) D.g (D.v i)
      (D.lower_cartesian i).w.symm).hom
    (rightSquare.{u, v} (D.toY_i i) (D.e_i i) D.e (D.toT_i i) (D.e_i_compatible i).symm)
    (rightSquare.{u, v} (D.u i) (D.f_i i) D.f (D.v i) (D.factorization i).symm)
    (rightSquare_cube D i) D.F

/-- **Stacks 0EZR, part (1): the base change map of sheaves of sets may be checked étale-locally
on `X`.**  Let

```
X <--h-- Y
|f       |e
S <--g-- T
```

be a cartesian square of schemes, let `{Uᵢ → X}` be an étale covering such that each `Uᵢ → S`
factors as `Uᵢ → Vᵢ → S` with `Vᵢ → S` étale, and form the induced cartesian squares with
`Yᵢ = Uᵢ ×_X Y` and `Tᵢ = Vᵢ ×_S T`.  If for every `i` the base change map
`fᵢ^{-1} g_{i,*} Fᵢ ⟶ h_{i,*} e_i^{-1} Fᵢ` of the `i`-th local square is an isomorphism, where
`Fᵢ` is the inverse image of `F` on `Tᵢ`, then the base change map
`f^{-1} g_* F ⟶ h_* e^{-1} F` of the outer square is an isomorphism. -/
@[stacks 0EZR "clause (1), for sheaves of SETS, which is the generality in which the source \
states it: the étale-local criterion for the ordinary base change map. Clause (2), the \
analogue for an object of the unbounded derived category, and clause (3), the analogue for the \
higher direct images, are not proved here."]
public theorem isIso_smallEtaleSetsBaseChange_of_isIso_local
    (D : EtaleLocalBaseChangeData.{u, z, max (u + 1) v, (max (u + 1) v) + 1}
      (Type (max (u + 1) v)))
    (hlocal : ∀ i : D.I,
      IsIso ((smallEtaleSetsBaseChange.{u, v} (D.e_i i) (D.h_i i) (D.g_i i) (D.f_i i)
        (D.local_cartesian i).w.symm).app
        ((smallEtaleInverseImage.{u, v} (D.toT_i i)).obj D.F))) :
    IsIso ((smallEtaleSetsBaseChange.{u, v} D.e D.h D.g D.f D.cartesian.w.symm).app D.F) := by
  rw [smallEtaleSetsBaseChange_eq.{u, v} D.e D.h D.g D.f D.cartesian.w.symm]
  have hcoverData :=
    (Scheme.ofArrows_mem_precoverage_iff (P := @Etale)
      (X := D.U) (f := D.u)).1 (by
        simpa [Scheme.etalePrecoverage] using D.cover)
  let U : D.I → D.X.Etale := fun i => by
    let : Etale (D.u i) := hcoverData.2 i
    exact Scheme.Etale.mk (D.u i)
  let one : D.X.Etale := Scheme.Etale.mk (𝟙 D.X)
  have hone : IsTerminal one := by
    refine IsTerminal.ofUniqueHom (fun Z => MorphismProperty.Over.homMk Z.hom) fun Z m => ?_
    apply MorphismProperty.Over.Hom.ext
    show m.left = Z.hom
    simpa [one, Scheme.Etale.mk, MorphismProperty.Over.mk,
      MorphismProperty.Over.homMk, CategoryTheory.Over.homMk] using
      (MorphismProperty.Over.w m)
  let a : ∀ i, U i ⟶ one := fun i => MorphismProperty.Over.homMk (D.u i)
  have hU : (smallEtaleTopology D.X).CoversTop U := by
    rw [GrothendieckTopology.coversTop_iff_of_isTerminal
      (J := smallEtaleTopology D.X) (X := one) (hX := hone),
      ← Sieve.ofArrows_eq_ofObjects hone U a, Scheme.ofArrows_mem_smallEtaleTopology_iff]
    show (⋃ i, Set.range (D.u i)) = Set.univ
    exact Set.eq_univ_iff_forall.2 fun x => by
      simpa only [Set.mem_iUnion, Set.mem_range] using hcoverData.1 x
  refine Sheaf.isIso_of_coversTop hU fun i => ?_
  apply isIso_overPullback_of_restriction (U i) _
  have : Etale (D.u i) := hcoverData.2 i
  exact localBaseChange_isIso D i (hlocal i)

end OrdinaryLocal

end Stacks.EtaleCohomology

end
