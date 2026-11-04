module

public import StacksFrontier.AlgebraicGeometry.Quot.ProjectiveQuot.Twist
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.PullbackTensorAlongAComposite
public import StacksFrontier.Topology.Sheaves.Cohomology.DerivedPullback.CompositionComplexLevel

/-!
# The base change of twists on `ℙⁿ_T` is compatible with composition

For `h : T'' ⟶ T'` and `g : T' ⟶ T`, the identification
`AlgebraicGeometry.ProjectiveQuot.twistPullbackIso` of `(g^* ℱ)(d)` with `g^*(ℱ(d))` along the
base change `ℙⁿ_{T'} ⟶ ℙⁿ_T` is compatible with the composition law `h^* g^* ≅ (h ≫ g)^*` of
pullback. This is the twist analogue of
`AlgebraicGeometry.ProjectiveQuot.freeModulePullbackIso_inv_comp`.

## Main results

* `AlgebraicGeometry.ProjectiveQuotOverSpace.comparison_pullbackComp_pullbackCongr`: the
  comparison of Stacks 01CD is compatible with `AlgebraicGeometry.Scheme.Modules.pullbackComp`,
  read through `AlgebraicGeometry.Scheme.Modules.pullbackCongr`.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.twistingSheafPullbackIso_comp`: the
  identifications `g^* 𝒪(d) ≅ 𝒪(d)` are compatible with composition.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.twistPullbackIso_hom_comp`: the identifications
  `(g^* ℱ)(d) ≅ g^*(ℱ(d))` are compatible with composition.
* `AlgebraicGeometry.ProjectiveQuotOverSpace.twistPullbackIso_hom_id`: along the identity of `T`
  the identification `(𝟙^* ℱ)(d) ≅ 𝟙^*(ℱ(d))` is the identity law `𝟙^* ≅ 𝟭`.

## Implementation notes

The two coherences are first proved for abstract bifunctors and functors
(`AlgebraicGeometry.ProjectiveQuotOverSpace.bifunctorPullbackIso_comp` and
`AlgebraicGeometry.ProjectiveQuotOverSpace.bifunctorPullbackIso_id`), where every isomorphism is a
free variable, and only then specialised: rewriting directly in the sheaf-tensor spelling fails,
because that spelling is not type-correct at the transparency `rw` checks motives at. The identity
case needs no comparison of `AlgebraicGeometry.Scheme.Modules.pullbackId` with the ringed-space
identity law: it follows from the composition case at `𝟙 ≫ 𝟙 = 𝟙`, the right unitality of the
pullback pseudofunctor and naturality.

## References

* [Stacks Project, Tag 01CD](https://stacks.math.columbia.edu/tag/01CD)
* [Stacks Project, Tag 0DPB](https://stacks.math.columbia.edu/tag/0DPB)
-/

@[expose] public noncomputable section

open CategoryTheory

universe u

namespace AlgebraicGeometry.ProjectiveQuotOverSpace

open AlgebraicGeometry.ProjectiveQuot
open Stacks.RingedSpace (comparisonBifunctorIso)

/-- The composition law `f^* g^* ⟶ k^*` of pullback along `f ≫ g = k`, at a module. -/
abbrev pullbackCompCongrApp {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z}
    (w : f ≫ g = k) (A : Z.Modules) :
    (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj A) ⟶
      (Scheme.Modules.pullback k).obj A :=
  (Scheme.Modules.pullbackComp f g).hom.app A ≫ (Scheme.Modules.pullbackCongr w).hom.app A

/-- **The comparison of Stacks 01CD is compatible with the composition law for pullback of
modules on schemes.** This is `Stacks.PullbackTensorComposition.comparison_comp`, read through
`Stacks.Scheme.Modules.pullbackComp_eq_modulePullbackComp`. -/
@[reassoc]
theorem comparison_pullbackComp_pullbackCongr {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z)
    {k : X ⟶ Z} (w : f ≫ g = k) (A B : Z.Modules) :
    pullbackCompCongrApp f g w ((Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
        ⟨Z.toSheafedSpace.presheaf, Z.toSheafedSpace.IsSheaf⟩)).obj (A, B)) ≫
        (comparisonBifunctorIso k.toLRSHom.toShHom).hom.app (A, B) =
      (Scheme.Modules.pullback f).map
          ((comparisonBifunctorIso g.toLRSHom.toShHom).hom.app (A, B)) ≫
        (comparisonBifunctorIso f.toLRSHom.toShHom).hom.app
          ((Scheme.Modules.pullback g).obj A, (Scheme.Modules.pullback g).obj B) ≫
        (Functor.uncurry.obj (Stacks.SheafOfModules.Tensor.sheafTensor
          ⟨X.toSheafedSpace.presheaf, X.toSheafedSpace.IsSheaf⟩)).map
          ((pullbackCompCongrApp f g w A, pullbackCompCongrApp f g w B) :
            ((Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj A),
              (Scheme.Modules.pullback f).obj ((Scheme.Modules.pullback g).obj B)) ⟶
            ((Scheme.Modules.pullback k).obj A, (Scheme.Modules.pullback k).obj B)) := by
  subst w
  have h := Stacks.PullbackTensorComposition.comparison_comp f.toLRSHom.toShHom
    g.toLRSHom.toShHom A B
  rw [← Stacks.Scheme.Modules.pullbackComp_eq_modulePullbackComp] at h
  simp only [pullbackCompCongrApp, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id]
  exact h

/-- **The pseudofunctor associativity of pullback, read along equalities of morphisms**: for
`f ≫ g = k`, `g ≫ p = q`, `f ≫ q = r` and `k ≫ p = r`, the two identifications
`f^* g^* p^* L ≅ r^* L` agree. -/
@[reassoc]
theorem pullbackCompCongrApp_assoc {X Y Z W : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) {k : X ⟶ Z}
    (w : f ≫ g = k) {p : Z ⟶ W} {q : Y ⟶ W} {r : X ⟶ W} (wg : g ≫ p = q) (wf : f ≫ q = r)
    (wk : k ≫ p = r) (L : W.Modules) :
    (Scheme.Modules.pullback f).map (pullbackCompCongrApp g p wg L) ≫
        pullbackCompCongrApp f q wf L =
      pullbackCompCongrApp f g w ((Scheme.Modules.pullback p).obj L) ≫
        pullbackCompCongrApp k p wk L := by
  subst w wg wf
  have key := NatTrans.congr_app (Scheme.Modules.pseudofunctor_associativity f g p) L
  simp only [NatTrans.comp_app, Functor.whiskerRight_app, Functor.associator_hom_app,
    Functor.whiskerLeft_app, Category.id_comp, eqToHom_app] at key
  simp only [pullbackCompCongrApp, Scheme.Modules.pullbackCongr, eqToIso_refl, Iso.refl_hom,
    NatTrans.id_app, Category.comp_id, eqToIso.hom, eqToHom_app]
  rw [← Iso.app_inv (Scheme.Modules.pullbackComp f (g ≫ p)) L, Iso.inv_comp_eq,
    ← Iso.app_inv (Scheme.Modules.pullbackComp g p) L, ← Functor.mapIso_inv,
    Iso.inv_comp_eq] at key
  simp only [Functor.mapIso_hom, Iso.app_hom] at key
  simp [reassoc_of% key]

/-- **Untwisting is compatible with composition, for abstract bifunctors.** Let `H_X`, `H_Y`,
`H_Z` be bifunctors, `P_f`, `P_g`, `P_k` functors with comparisons
`c : P(H(A, B)) ≅ H(P A, P B)`, and `ψ : P_g ⋙ P_f ⟶ P_k` compatible with the comparisons at
`(F, L_Z)`. Given identifications `τ_g : P_g L_Z ≅ L_Y`, `τ_f : P_f L_Y ≅ L_X` and
`τ_k : P_k L_Z ≅ L_X` compatible with `ψ`, the identifications
`H(P F, L) ≅ P (H(F, L_Z))` built from `c` and `τ` are compatible with `ψ`. -/
@[reassoc]
theorem bifunctorPullbackIso_comp {CX CY CZ : Type*} [Category* CX] [Category* CY]
    [Category* CZ] (HX : CX × CX ⥤ CX) (HY : CY × CY ⥤ CY) (HZ : CZ × CZ ⥤ CZ)
    (Pf : CY ⥤ CX) (Pg : CZ ⥤ CY) (Pk : CZ ⥤ CX) (cf : HY ⋙ Pf ≅ Pf.prod Pf ⋙ HX)
    (cg : HZ ⋙ Pg ≅ Pg.prod Pg ⋙ HY) (ck : HZ ⋙ Pk ≅ Pk.prod Pk ⋙ HX) (ψ : Pg ⋙ Pf ⟶ Pk)
    {LX : CX} {LY : CY} {LZ : CZ} (F : CZ)
    (hc : ψ.app (HZ.obj (F, LZ)) ≫ ck.hom.app (F, LZ) =
      Pf.map (cg.hom.app (F, LZ)) ≫ cf.hom.app (Pg.obj F, Pg.obj LZ) ≫
        HX.map ((ψ.app F, ψ.app LZ) : (Pf.obj (Pg.obj F), Pf.obj (Pg.obj LZ)) ⟶
          (Pk.obj F, Pk.obj LZ)))
    (τg : Pg.obj LZ ≅ LY) (τf : Pf.obj LY ≅ LX) (τk : Pk.obj LZ ≅ LX)
    (hτ : Pf.map τg.hom ≫ τf.hom = ψ.app LZ ≫ τk.hom) :
    HX.map ((ψ.app F, 𝟙 LX) : (Pf.obj (Pg.obj F), LX) ⟶ (Pk.obj F, LX)) ≫
        (HX.mapIso (Iso.prod (Iso.refl (Pk.obj F)) τk.symm) ≪≫ (ck.app (F, LZ)).symm).hom =
      (HX.mapIso (Iso.prod (Iso.refl (Pf.obj (Pg.obj F))) τf.symm) ≪≫
          (cf.app (Pg.obj F, LY)).symm).hom ≫
        Pf.map (HY.mapIso (Iso.prod (Iso.refl (Pg.obj F)) τg.symm) ≪≫
          (cg.app (F, LZ)).symm).hom ≫
        ψ.app (HZ.obj (F, LZ)) := by
  rw [Iso.trans_hom, Iso.symm_hom, ← Category.assoc, Iso.comp_inv_eq]
  simp only [Iso.trans_hom, Iso.symm_hom, Iso.app_inv, Iso.app_hom, Functor.mapIso_hom,
    Functor.map_comp, Category.assoc]
  rw [hc, ← Pf.map_comp_assoc (cg.inv.app (F, LZ)) (cg.hom.app (F, LZ)), Iso.inv_hom_id_app,
    CategoryTheory.Functor.map_id, Category.id_comp]
  have nat : Pf.map (HY.map (Iso.prod (Iso.refl (Pg.obj F)) τg.symm).hom) ≫
      cf.hom.app (Pg.obj F, Pg.obj LZ) =
      cf.hom.app (Pg.obj F, LY) ≫
        HX.map ((Pf.prod Pf).map (Iso.prod (Iso.refl (Pg.obj F)) τg.symm).hom) :=
    cf.hom.naturality _
  rw [reassoc_of% nat, Iso.inv_hom_id_app_assoc, ← Functor.map_comp, ← Functor.map_comp,
    ← Functor.map_comp]
  congr 1
  refine Prod.ext ?_ ?_
  · show ψ.app F ≫ 𝟙 _ = 𝟙 _ ≫ Pf.map (𝟙 _) ≫ ψ.app F
    simp
  · show 𝟙 _ ≫ τk.inv = τf.inv ≫ Pf.map τg.inv ≫ ψ.app LZ
    rw [Category.id_comp, ← cancel_mono τk.hom, Category.assoc, Category.assoc, ← hτ,
      Iso.inv_hom_id, ← Functor.map_comp_assoc, Iso.inv_hom_id, CategoryTheory.Functor.map_id,
      Category.id_comp, Iso.inv_hom_id]

/-- **Untwisting along an endofunctor isomorphic to the identity is the identity, for abstract
bifunctors.** Let `ι : P ≅ 𝟭` and let `θ G : H(P G, L) ≅ P (H(G, L))` be natural in `G` and
compatible with a family `ψ G : P (P G) ⟶ P G` which is `ι` at `P G`. Then `θ` is `ι`: the map
`H(ι, 𝟙) : H(P G, L) ⟶ H(G, L)` is `θ G` followed by `ι`. -/
theorem bifunctorPullbackIso_id {C : Type*} [Category* C] (H : C × C ⥤ C) (P : C ⥤ C)
    (ι : P ≅ 𝟭 C) (L : C) (θ : ∀ G : C, H.obj (P.obj G, L) ≅ P.obj (H.obj (G, L)))
    (hθ : ∀ {G G' : C} (φ : G ⟶ G'),
      H.map ((P.map φ, 𝟙 L) : (P.obj G, L) ⟶ (P.obj G', L)) ≫ (θ G').hom =
        (θ G).hom ≫ P.map (H.map ((φ, 𝟙 L) : (G, L) ⟶ (G', L))))
    (ψ : ∀ G : C, P.obj (P.obj G) ⟶ P.obj G) (hψ : ∀ G : C, ψ G = ι.hom.app (P.obj G))
    (hcomp : ∀ G : C,
      H.map ((ψ G, 𝟙 L) : (P.obj (P.obj G), L) ⟶ (P.obj G, L)) ≫ (θ G).hom =
        (θ (P.obj G)).hom ≫ P.map (θ G).hom ≫ ψ (H.obj (G, L)))
    (G : C) :
    H.map ((ι.hom.app G, 𝟙 L) : (P.obj G, L) ⟶ (G, L)) =
      (θ G).hom ≫ ι.hom.app (H.obj (G, L)) := by
  have nat : ∀ {A B : C} (f : A ⟶ B), P.map f ≫ ι.hom.app B = ι.hom.app A ≫ f := fun f => by
    simp
  have hA : H.map ((ι.hom.app (P.obj G), 𝟙 L) : (P.obj (P.obj G), L) ⟶ (P.obj G, L)) =
      (θ (P.obj G)).hom ≫ ι.hom.app (H.obj (P.obj G, L)) := by
    have h := hcomp G
    rw [hψ, hψ, nat, ← Category.assoc] at h
    exact (cancel_mono (θ G).hom).1 h
  have h1 := hθ (ι.hom.app G)
  rw [(cancel_mono _).1 (nat (ι.hom.app G)), hA, Category.assoc] at h1
  have h2 := (cancel_epi (θ (P.obj G)).hom).1 h1
  have h3 := nat (H.map ((ι.hom.app G, 𝟙 L) : (P.obj G, L) ⟶ (G, L)))
  rw [← h2, Category.assoc] at h3
  exact ((cancel_epi _).1 h3).symm

/-- **The composition law of pullback along an endomorphism equal to the identity is the
identity law**: for `p = 𝟙` and `p ≫ p = p`, the composite `p^* p^* ⟶ (p ≫ p)^* ⟶ p^*` at a
module `M` is the identification `p^* ≅ 𝟭` at `p^* M`. -/
theorem pullbackComp_pullbackCongr_eq_pullbackId {X : Scheme.{u}} (p : X ⟶ X) (e : p = 𝟙 X)
    (q : p ≫ p = p) (M : X.Modules) :
    (Scheme.Modules.pullbackComp p p).hom.app M ≫ (Scheme.Modules.pullbackCongr q).hom.app M =
      (Scheme.Modules.pullbackCongr e).hom.app ((Scheme.Modules.pullback p).obj M) ≫
        (Scheme.Modules.pullbackId X).hom.app ((Scheme.Modules.pullback p).obj M) := by
  subst e
  have key := NatTrans.congr_app (Scheme.Modules.pseudofunctor_right_unitality (𝟙 X)) M
  simp only [NatTrans.comp_app, Functor.whiskerLeft_app, Functor.rightUnitor_hom_app,
    eqToHom_app] at key
  rw [← Iso.app_inv (Scheme.Modules.pullbackComp (𝟙 X) (𝟙 X)) M, Iso.inv_comp_eq] at key
  simp only [Iso.app_hom] at key
  simp only [Scheme.Modules.pullbackCongr, eqToIso.hom, eqToHom_app]
  exact ((Category.comp_id _).symm.trans key).symm

variable {n : ℕ}

variable (n) in
/-- **The identifications `g^* 𝒪(d) ≅ 𝒪(d)` on `ℙⁿ` are compatible with composition.** -/
@[reassoc]
theorem twistingSheafPullbackIso_comp {T'' T' T : Scheme.{u}} (h : T'' ⟶ T') (g : T' ⟶ T)
    (d : ℤ) :
    (Scheme.Modules.pullback (projectiveSpaceOverMap n h)).map
        (ProjectiveQuot.twistingSheafPullbackIso n g d).hom ≫
        (ProjectiveQuot.twistingSheafPullbackIso n h d).hom =
      ((Scheme.Modules.pullbackComp (projectiveSpaceOverMap n h)
          (projectiveSpaceOverMap n g)).hom.app (ProjectiveQuot.twistingSheaf n T d) ≫
        (Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_comp n h g)).hom.app
          (ProjectiveQuot.twistingSheaf n T d)) ≫
        (ProjectiveQuot.twistingSheafPullbackIso n (h ≫ g) d).hom :=
  pullbackCompCongrApp_assoc (projectiveSpaceOverMap n h) (projectiveSpaceOverMap n g)
    (projectiveSpaceOverMap_comp n h g) (projectiveSpaceOverMap_snd n g)
    (projectiveSpaceOverMap_snd n h) (projectiveSpaceOverMap_snd n (h ≫ g)) _

/-- **The identifications `(g^* ℱ)(d) ≅ g^*(ℱ(d))` on `ℙⁿ` are compatible with composition**:
for `h : T'' ⟶ T'` and `g : T' ⟶ T`, reading `h^* g^* ℱ` as `(h ≫ g)^* ℱ` and then untwisting the
pullback along `h ≫ g` agrees with untwisting along `h`, then along `g`, and then reading
`h^* g^*(ℱ(d))` as `(h ≫ g)^*(ℱ(d))`. -/
@[reassoc]
theorem twistPullbackIso_hom_comp {T'' T' T : Scheme.{u}} (h : T'' ⟶ T') (g : T' ⟶ T) (d : ℤ)
    (F : (projectiveSpaceOver n T).Modules) :
    ProjectiveQuot.twistMap d ((Scheme.Modules.pullbackComp (projectiveSpaceOverMap n h)
          (projectiveSpaceOverMap n g)).hom.app F ≫
        (Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_comp n h g)).hom.app F) ≫
        (ProjectiveQuot.twistPullbackIso (h ≫ g) d F).hom =
      (ProjectiveQuot.twistPullbackIso h d
          ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj F)).hom ≫
        (Scheme.Modules.pullback (projectiveSpaceOverMap n h)).map
          (ProjectiveQuot.twistPullbackIso g d F).hom ≫
        (Scheme.Modules.pullbackComp (projectiveSpaceOverMap n h)
          (projectiveSpaceOverMap n g)).hom.app (ProjectiveQuot.twist d F) ≫
        (Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_comp n h g)).hom.app
          (ProjectiveQuot.twist d F) :=
  bifunctorPullbackIso_comp _ _ _ _ _ _ _ _ _
    ((Scheme.Modules.pullbackComp (projectiveSpaceOverMap n h) (projectiveSpaceOverMap n g)).hom ≫
      (Scheme.Modules.pullbackCongr (projectiveSpaceOverMap_comp n h g)).hom) F
    (comparison_pullbackComp_pullbackCongr _ _ (projectiveSpaceOverMap_comp n h g) F _)
    (ProjectiveQuot.twistingSheafPullbackIso n g d) (ProjectiveQuot.twistingSheafPullbackIso n h d)
    (ProjectiveQuot.twistingSheafPullbackIso n (h ≫ g) d) (twistingSheafPullbackIso_comp n h g d)

/-- `AlgebraicGeometry.ProjectiveQuotOverSpace.twistPullbackIso_hom_comp` along a composite
`h ≫ g = k` given by an equation, so that `k` need not be syntactically `h ≫ g`. -/
@[reassoc]
theorem twistPullbackIso_hom_comp_of_eq {T'' T' T : Scheme.{u}} (h : T'' ⟶ T') (g : T' ⟶ T)
    {k : T'' ⟶ T} (w : h ≫ g = k) (d : ℤ) (F : (projectiveSpaceOver n T).Modules) :
    ProjectiveQuot.twistMap d ((Scheme.Modules.pullbackComp (projectiveSpaceOverMap n h)
          (projectiveSpaceOverMap n g)).hom.app F ≫
        (Scheme.Modules.pullbackCongr ((projectiveSpaceOverMap_comp n h g).trans
          (congrArg (projectiveSpaceOverMap n) w))).hom.app F) ≫
        (ProjectiveQuot.twistPullbackIso k d F).hom =
      (ProjectiveQuot.twistPullbackIso h d
          ((Scheme.Modules.pullback (projectiveSpaceOverMap n g)).obj F)).hom ≫
        (Scheme.Modules.pullback (projectiveSpaceOverMap n h)).map
          (ProjectiveQuot.twistPullbackIso g d F).hom ≫
        (Scheme.Modules.pullbackComp (projectiveSpaceOverMap n h)
          (projectiveSpaceOverMap n g)).hom.app (ProjectiveQuot.twist d F) ≫
        (Scheme.Modules.pullbackCongr ((projectiveSpaceOverMap_comp n h g).trans
          (congrArg (projectiveSpaceOverMap n) w))).hom.app (ProjectiveQuot.twist d F) := by
  subst w
  exact twistPullbackIso_hom_comp h g d F

/-- **Along the identity of `T`, the identification `(𝟙^* ℱ)(d) ≅ 𝟙^*(ℱ(d))` is the identity**:
twisting the identification `𝟙^* ℱ ≅ ℱ` of `ℙⁿ_T ⟶ ℙⁿ_T` is `twistPullbackIso (𝟙 T)` followed by
the identification `𝟙^*(ℱ(d)) ≅ ℱ(d)`. -/
theorem twistPullbackIso_hom_id {T : Scheme.{u}} (d : ℤ) (F : (projectiveSpaceOver n T).Modules) :
    ProjectiveQuot.twistMap d
        ((ProjectiveQuot.pullbackProjectiveSpaceOverMapIdIso n T).hom.app F) =
      (ProjectiveQuot.twistPullbackIso (𝟙 T) d F).hom ≫
        (ProjectiveQuot.pullbackProjectiveSpaceOverMapIdIso n T).hom.app
          (ProjectiveQuot.twist d F) :=
  bifunctorPullbackIso_id _ (Scheme.Modules.pullback (projectiveSpaceOverMap n (𝟙 T)))
    (ProjectiveQuot.pullbackProjectiveSpaceOverMapIdIso n T)
    (ProjectiveQuot.twistingSheaf n T d) (fun G => ProjectiveQuot.twistPullbackIso (𝟙 T) d G)
    (fun φ => ProjectiveQuot.twistPullbackIso_hom_naturality (𝟙 T) d φ)
    (fun G => (Scheme.Modules.pullbackComp (projectiveSpaceOverMap n (𝟙 T))
          (projectiveSpaceOverMap n (𝟙 T))).hom.app G ≫
        (Scheme.Modules.pullbackCongr ((projectiveSpaceOverMap_comp n (𝟙 T) (𝟙 T)).trans
          (congrArg (projectiveSpaceOverMap n) (Category.id_comp (𝟙 T))))).hom.app G)
    (fun G => pullbackComp_pullbackCongr_eq_pullbackId _ (projectiveSpaceOverMap_id n T) _ G)
    (fun G => twistPullbackIso_hom_comp_of_eq (𝟙 T) (𝟙 T) (Category.id_comp (𝟙 T)) d G) F

end AlgebraicGeometry.ProjectiveQuotOverSpace

end
