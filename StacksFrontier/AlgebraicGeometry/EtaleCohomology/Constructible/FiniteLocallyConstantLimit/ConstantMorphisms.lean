module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafHom
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.Constructible.FiniteLocallyConstantLimit.Basic
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EnoughGeometricPoints
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.ConstantSheafAbelian

/-!
# Morphisms between constant sheaves on a small étale site

Let `S` be an object of a big étale site and let `E`, `E'` be sets, abelian groups or modules
over a ring `Λ`. This file proves three facts about morphisms between the constant sheaves on
`E` and `E'` on the small étale site of `S`, each stated through the inverse image along the
structure morphism of an étale `S`-scheme and the identification
`AlgebraicGeometry.smallEtaleConstantPullbackIso` of the inverse image of a constant sheaf with
the constant sheaf.

* A morphism `a` from the constant sheaf on `E` to the constant sheaf on `E'`, with `E` finite
  (sets, abelian groups) or finitely generated (modules), is *locally constant*: there is an
  étale covering `{V_k → S}` and maps `g_k : E ⟶ E'` such that the inverse image of `a` to each
  `V_k` is the constant sheaf map attached to `g_k`. This is the case of Stacks Tag 093S for
  constant sheaves, read through inverse images instead of restrictions to localized sites.
* The constant sheaf functor is faithful as soon as `S` is nonempty.
* Inverse image commutes with constant sheaf maps.

## Strategy

The bridge between local information on the site of `S` and the inverse image to an étale
`S`-scheme `V` is `Stacks.ConstantSheaf.sheafPullback_map_eq_of_toSheafify_app_comp_eq`. On an
arbitrary site, a morphism out of a constant sheaf is determined by its adjoint transpose, the
composite with the unit at the final object (`CategoryTheory.constantSheafAdj`). The comparison
of the inverse image of a constant sheaf with the constant sheaf is the uniqueness of left
adjoints, so it is characterized by its effect on units as well. Computing the transpose of the
inverse image of `a`, the restriction to `V` appears as soon as the final object of the target
site maps to the image of `V` — for the small étale site this is the diagonal section
`AlgebraicGeometry.smallEtaleFinalToBaseChangeSelf` of `V ×_S V → V`. The upshot: the inverse
image of `a` to `V` is the constant map attached to `g` as soon as `a` sends the constant section
of `E` over `V` to the constant section attached by `g`, an equality of maps
`E ⟶ Γ(V, E'_S)` with no inverse image in it.

That local condition is then produced by local surjectivity of sheafification (each of the
finitely many sections `a(x)`, for `x` running over the elements or generators of `E`, is
constant on a covering), and the maps `g_k` are made additive or linear using that a constant
section over a *nonempty* étale `S`-scheme determines its value: the empty members of a covering
are dropped, and over a nonempty member a geometric point separates constants
(`AlgebraicGeometry.injective_toSheafify_app_const_of_nonempty`). This is why no finite
presentation is needed for modules, unlike Tag 093S on a general site.

## Main results

* `Stacks.ConstantSheaf.sheafPullback_map_eq_of_toSheafify_app_comp_eq` — on general sites, a
  morphism of constant sheaves whose transpose is constant over an object whose image receives
  the final object has constant inverse image.
* `AlgebraicGeometry.smallEtaleSheafPullback_map_eq_of_toSheafify_app_comp_eq` — the same on
  small étale sites, for the inverse image along the structure morphism of `V`.
* `AlgebraicGeometry.smallEtaleSheafPullback_map_constantSheaf_map` — inverse image commutes
  with constant sheaf maps.
* `AlgebraicGeometry.exists_cover_smallEtaleSheafPullback_map_eq_type`,
  `AlgebraicGeometry.exists_cover_smallEtaleSheafPullback_map_eq_addCommGrpCat` and
  `AlgebraicGeometry.exists_cover_smallEtaleSheafPullback_map_eq_moduleCat` — morphisms of
  constant sheaves with finite (finitely generated) source are locally constant.
* `AlgebraicGeometry.smallEtale_constantSheaf_map_injective` and its three specializations — the
  constant sheaf functor is faithful on a nonempty scheme.

## Implementation notes

`AlgebraicGeometry.smallEtaleConstantPullbackIso` takes the adjointness of direct image as a
family over all morphisms of the big étale site. Typeclass inference finds each member but not
the family, so the three coefficient categories get the per-morphism statements
`AlgebraicGeometry.SmallEtale.isRightAdjointPushforward_type`,
`AlgebraicGeometry.SmallEtale.isRightAdjointPushforward_addCommGrpCat` and
`AlgebraicGeometry.SmallEtale.isRightAdjointPushforward_moduleCat_site`, used as local instances.

## References

* [Stacks Project, Tag 093S](https://stacks.math.columbia.edu/tag/093S)
* [Stacks Project, Tag 093R](https://stacks.math.columbia.edu/tag/093R)
* [Stacks Project, Tag 0GL2](https://stacks.math.columbia.edu/tag/0GL2)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe w t v u v' u'

namespace Stacks.ConstantSheaf

section General

variable {C : Type u} [Category.{v} C] {D : Type u'} [Category.{v'} D]
  (F : C ⥤ D) (A : Type w) [Category.{t} A]
  (J : GrothendieckTopology C) (K : GrothendieckTopology D)
  [Functor.IsContinuous F J K]
  [(F.sheafPushforwardContinuous A J K).IsRightAdjoint]
  [HasWeakSheafify J A] [HasWeakSheafify K A]

/-- **A morphism of constant sheaves which is constant over `U` has constant inverse image.**
Let `F : C ⥤ D` be a continuous functor with an inverse image, carrying the final object `T` of
`C` to the final object `T'` of `D`, and let `U` be an object of `C` such that `T'` maps to
`F.obj U`. If `a` sends the constant section of `E` over `U` to the constant section attached by
`g : E ⟶ E'`, then the inverse image of `a` is the constant sheaf map attached to `g`, under the
identification `Stacks.ConstantSheaf.sheafPullbackConstantSheafIso`.

Both sides are compared through their transposes under the constant sheaf adjunction at `T'`:
the comparison isomorphism is a uniqueness of left adjoints, so it matches the two units, and
the transpose of the inverse image of `a` is read off from sections over `T`, then restricted to
`U` and pulled back along `T' ⟶ F.obj U`. -/
public theorem sheafPullback_map_eq_of_toSheafify_app_comp_eq {T : C} (hT : IsTerminal T)
    {T' : D} (hT' : IsTerminal T') (e : F.obj T ≅ T') {E E' : A}
    (a : (constantSheaf J A).obj E ⟶ (constantSheaf J A).obj E') (g : E ⟶ E') {U : C}
    (s : T' ⟶ F.obj U)
    (h : (toSheafify J ((Functor.const Cᵒᵖ).obj E)).app (op U) ≫ a.hom.app (op U) =
      g ≫ (toSheafify J ((Functor.const Cᵒᵖ).obj E')).app (op U)) :
    (F.sheafPullback A J K).map a =
      ((sheafPullbackConstantSheafIso F A J K hT hT' e).app E).hom ≫
        (constantSheaf K A).map g ≫
          ((sheafPullbackConstantSheafIso F A J K hT hT' e).app E').inv := by
  have hc : sheafPullbackConstantSheafIso F A J K hT hT' e =
      (((constantSheafAdj J A hT).comp (F.sheafAdjunctionContinuous A J K)).ofNatIsoRight
        (pushforwardSectionsIsoOfTerminal F A J K e)).leftAdjointUniq
          (constantSheafAdj K A hT') := rfl
  -- the transpose of a morphism out of the inverse image of a constant sheaf
  have hunit : ∀ (X : A) (Y : Sheaf K A) (φ : (F.sheafPullback A J K).obj
      ((constantSheaf J A).obj X) ⟶ Y),
      (((constantSheafAdj J A hT).comp (F.sheafAdjunctionContinuous A J K)).ofNatIsoRight
        (pushforwardSectionsIsoOfTerminal F A J K e)).unit.app X ≫
          ((sheafSections K A).obj (op T')).map φ =
        (toSheafify J ((Functor.const Cᵒᵖ).obj X)).app (op T) ≫
          ((F.sheafAdjunctionContinuous A J K).unit.app _ ≫
            (F.sheafPushforwardContinuous A J K).map φ).hom.app (op T) ≫
            (pushforwardSectionsIsoOfTerminal F A J K e).hom.app Y := by
    intro X Y φ
    refine (Adjunction.homEquiv_unit
      (((constantSheafAdj J A hT).comp (F.sheafAdjunctionContinuous A J K)).ofNatIsoRight
        (pushforwardSectionsIsoOfTerminal F A J K e)) X Y φ).symm.trans ?_
    rw [Adjunction.homEquiv_ofNatIsoRight_apply, Adjunction.comp_homEquiv]
    simp only [Equiv.trans_apply, Adjunction.homEquiv_unit, constantSheafAdj_unit_app]
    exact Category.assoc _ _ _
  -- the comparison on sections over the final object factors through sections over `U`
  set ν := (F.sheafAdjunctionContinuous A J K).unit with hν
  set G := (F.sheafPullback A J K).obj ((constantSheaf J A).obj E') with hG
  set τ := hT.from U with hτ
  have hTF : IsTerminal (F.obj T) := hT'.ofIso e.symm
  have he : e.inv = s ≫ F.map τ := hTF.hom_ext _ _
  have hθ : (ν.app ((constantSheaf J A).obj E')).hom.app (op T) ≫
      (pushforwardSectionsIsoOfTerminal F A J K e).hom.app G =
      ((constantSheaf J A).obj E').obj.map τ.op ≫
        (ν.app ((constantSheaf J A).obj E')).hom.app (op U) ≫ G.obj.map s.op := by
    have h1 : (pushforwardSectionsIsoOfTerminal F A J K e).hom.app G = G.obj.map e.inv.op := rfl
    rw [h1, he, op_comp, Functor.map_comp]
    exact (Category.assoc _ _ _).symm.trans
      (((ν.app ((constantSheaf J A).obj E')).hom.naturality τ.op =≫ G.obj.map s.op).symm.trans
        (Category.assoc _ _ _))
  have hη : ∀ X : A, (toSheafify J ((Functor.const Cᵒᵖ).obj X)).app (op T) ≫
      ((constantSheaf J A).obj X).obj.map τ.op =
        (toSheafify J ((Functor.const Cᵒᵖ).obj X)).app (op U) := by
    intro X
    exact ((toSheafify J ((Functor.const Cᵒᵖ).obj X)).naturality τ.op).symm.trans
      (Category.id_comp _)
  -- the transpose of the inverse image of `a`
  have key : (((constantSheafAdj J A hT).comp (F.sheafAdjunctionContinuous A J K)).ofNatIsoRight
        (pushforwardSectionsIsoOfTerminal F A J K e)).unit.app E ≫
          ((sheafSections K A).obj (op T')).map ((F.sheafPullback A J K).map a) =
      g ≫ (((constantSheafAdj J A hT).comp (F.sheafAdjunctionContinuous A J K)).ofNatIsoRight
        (pushforwardSectionsIsoOfTerminal F A J K e)).unit.app E' := by
    have k2 : (((constantSheafAdj J A hT).comp
        (F.sheafAdjunctionContinuous A J K)).ofNatIsoRight
          (pushforwardSectionsIsoOfTerminal F A J K e)).unit.app E' =
        (toSheafify J ((Functor.const Cᵒᵖ).obj E')).app (op T) ≫
          (ν.app ((constantSheaf J A).obj E')).hom.app (op T) ≫
            (pushforwardSectionsIsoOfTerminal F A J K e).hom.app G := by
      have := hunit E' G (𝟙 G)
      refine (Category.comp_id _).symm.trans (this.trans ?_)
      rw [CategoryTheory.Functor.map_id]
      erw [Category.comp_id]
    rw [hunit E _ ((F.sheafPullback A J K).map a), k2]
    have hnat := congrArg (fun φ => φ.hom.app (op T)) (ν.naturality a)
    simp only [Functor.id_map, Functor.comp_map, ObjectProperty.FullSubcategory.comp_hom,
      NatTrans.comp_app] at hnat
    have aux : ∀ {X X' PT PU QT QU HT GT GU Z : A} (ηT : X ⟶ PT) (ηU : X ⟶ PU) (rE : PT ⟶ PU)
        (η'T : X' ⟶ QT) (η'U : X' ⟶ QU) (r : QT ⟶ QU) (aT : PT ⟶ QT) (aU : PU ⟶ QU)
        (νET : PT ⟶ HT) (bT : HT ⟶ GT) (νT : QT ⟶ GT) (νU : QU ⟶ GU) (ι : GT ⟶ Z)
        (σ : GU ⟶ Z) (g : X ⟶ X') (hnat : aT ≫ νT = νET ≫ bT)
        (hθ : νT ≫ ι = r ≫ νU ≫ σ) (ha : rE ≫ aU = aT ≫ r) (hη : ηT ≫ rE = ηU)
        (hη' : η'T ≫ r = η'U) (h : ηU ≫ aU = g ≫ η'U),
        ηT ≫ (νET ≫ bT) ≫ ι = g ≫ η'T ≫ νT ≫ ι := by
      intros X X' PT PU QT QU HT GT GU Z ηT ηU rE η'T η'U r aT aU νET bT νT νU ι σ g hnat hθ
        ha hη hη' h
      rw [← hnat, Category.assoc, hθ, ← reassoc_of% ha, reassoc_of% hη, reassoc_of% h,
        ← reassoc_of% hη']
    exact aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ g hnat hθ (a.hom.naturality τ.op) (hη E) (hη E') h
  rw [hc, ← Category.assoc, Iso.eq_comp_inv]
  apply ((((constantSheafAdj J A hT).comp (F.sheafAdjunctionContinuous A J K)).ofNatIsoRight
    (pushforwardSectionsIsoOfTerminal F A J K e)).homEquiv _ _).injective
  rw [Adjunction.homEquiv_unit, Adjunction.homEquiv_unit, Functor.map_comp, Functor.map_comp,
    Iso.app_hom, Iso.app_hom, ← Category.assoc, key, ← Category.assoc, Category.assoc,
    Adjunction.unit_leftAdjointUniq_hom_app, Adjunction.unit_leftAdjointUniq_hom_app]
  exact (constantSheafAdj K A hT').unit.naturality g

end General

section Concrete

variable {C : Type u} [Category.{v} C] (J : GrothendieckTopology C)
  {A : Type w} [Category.{t} A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA] [HasWeakSheafify J A]

/-- **Finitely many sections of a constant sheaf are constant on a common covering.** For a
morphism `a` of constant sheaves and finitely many elements `x j` of `E`, there is a covering
sieve of `X` over each member of which every section `a(x j)` is the constant section attached
to some element of `E'`. This is local surjectivity of sheafification, for finitely many sections
at once. -/
public theorem exists_sieve_toSheafify_app_eq {E E' : A}
    [Presheaf.IsLocallySurjective J (toSheafify J ((Functor.const Cᵒᵖ).obj E'))]
    (a : (constantSheaf J A).obj E ⟶ (constantSheaf J A).obj E') {ι : Type*} [Finite ι]
    (x : ι → ToType E) (X : C) :
    ∃ R ∈ J X, ∀ (W : C) (f : W ⟶ X), R f → ∀ j, ∃ m : ToType E',
      (toSheafify J ((Functor.const Cᵒᵖ).obj E')).app (op W) m =
        a.hom.app (op W) ((toSheafify J ((Functor.const Cᵒᵖ).obj E)).app (op W) (x j)) := by
  classical
  have := Fintype.ofFinite ι
  let σ : ι → ToType (((constantSheaf J A).obj E').obj.obj (op X)) := fun j =>
    a.hom.app (op X) ((toSheafify J ((Functor.const Cᵒᵖ).obj E)).app (op X) (x j))
  let R : ι → Sieve X := fun j =>
    Presheaf.imageSieve (toSheafify J ((Functor.const Cᵒᵖ).obj E')) (σ j)
  have hR : ∀ s : Finset ι, s.inf R ∈ J X := by
    intro s
    induction s using Finset.induction_on with
    | empty => simp
    | @insert j s _ ih =>
      simpa using J.intersection_covering
        (Presheaf.imageSieve_mem J (toSheafify J ((Functor.const Cᵒᵖ).obj E')) (σ j)) ih
  refine ⟨Finset.univ.inf R, hR _, fun W f hf j => ?_⟩
  obtain ⟨m, hm⟩ := (Finset.inf_le (Finset.mem_univ j) : Finset.univ.inf R ≤ R j) _ hf
  refine ⟨m, hm.trans ?_⟩
  have hη := ConcreteCategory.congr_hom
    ((toSheafify J ((Functor.const Cᵒᵖ).obj E)).naturality f.op) (x j)
  simp only [CategoryTheory.comp_apply, Functor.const_obj_map] at hη
  have hid : ConcreteCategory.hom (𝟙 E) (x j) = x j := ConcreteCategory.id_apply _
  rw [hid] at hη
  rw [hη]
  exact (NatTrans.naturality_apply a.hom f.op _).symm

end Concrete

end Stacks.ConstantSheaf

namespace AlgebraicGeometry

section Diagonal

variable (B : BigEtaleSite.{u})

/-- **The diagonal section.** For an object `V` of the small étale site of `S`, the final object
of the small étale site of the scheme `V` maps to the base change of `V` along its own structure
morphism, by the diagonal `V ⟶ V ×_S V`. -/
public def smallEtaleFinalToBaseChangeSelf {S : B.Scheme} (V : SmallEtale B S.obj S.property) :
    SmallEtale.final B V.obj.left.obj V.obj.left.property ⟶
      (smallEtaleBaseChange B V.obj.hom).obj V :=
  ObjectProperty.homMk (Over.homMk (pullback.lift (𝟙 _) (𝟙 _) rfl) (pullback.lift_snd _ _ _))

end Diagonal

section Pullback

variable (B : BigEtaleSite.{u}) (A : Type t) [Category.{v} A]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]

/-- **A morphism of constant sheaves constant over `V` has constant inverse image to `V`.** If a
morphism `a` from the constant sheaf on `E` to the constant sheaf on `E'` on the small étale site
of `S` sends the constant section of `E` over `V` to the constant section attached by
`g : E ⟶ E'`, then its inverse image along the structure morphism of `V` is the constant sheaf
map attached to `g`, under `AlgebraicGeometry.smallEtaleConstantPullbackIso`.

This is `Stacks.ConstantSheaf.sheafPullback_map_eq_of_toSheafify_app_comp_eq` for base change
along the structure morphism of `V`, with the diagonal section
`AlgebraicGeometry.smallEtaleFinalToBaseChangeSelf`. -/
public theorem smallEtaleSheafPullback_map_eq_of_toSheafify_app_comp_eq {S : B.Scheme}
    (V : SmallEtale B S.obj S.property) {E E' : A}
    (a : (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E') (g : E ⟶ E')
    (h : (toSheafify (SmallEtale.topology B S.obj S.property)
          ((Functor.const _).obj E)).app (op V) ≫ a.hom.app (op V) =
      g ≫ (toSheafify (SmallEtale.topology B S.obj S.property)
          ((Functor.const _).obj E')).app (op V)) :
    (smallEtaleSheafPullback B A V.obj.hom).map a =
      (smallEtaleConstantPullbackIso B A V.obj.hom E).hom ≫
        (constantSheaf (SmallEtale.topology B V.obj.left.obj V.obj.left.property) A).map g ≫
          (smallEtaleConstantPullbackIso B A V.obj.hom E').inv :=
  Stacks.ConstantSheaf.sheafPullback_map_eq_of_toSheafify_app_comp_eq
    (smallEtaleBaseChange B V.obj.hom) A _ _
    (SmallEtale.finalIsTerminal B S.obj S.property)
    (SmallEtale.finalIsTerminal B V.obj.left.obj V.obj.left.property)
    (smallEtaleFinalBaseChangeIso B V.obj.hom) a g (smallEtaleFinalToBaseChangeSelf B V) h

/-- **Inverse image commutes with constant sheaf maps.** For `u : T ⟶ S` and `g : E ⟶ E'`, the
inverse image along `u` of the constant sheaf map attached to `g` is the constant sheaf map
attached to `g`, under `AlgebraicGeometry.smallEtaleConstantPullbackIso`: the latter is a
component of a natural isomorphism. -/
public theorem smallEtaleSheafPullback_map_constantSheaf_map {S T : B.Scheme} (u : T ⟶ S)
    {E E' : A} (g : E ⟶ E') :
    (smallEtaleSheafPullback B A u).map
        ((constantSheaf (SmallEtale.topology B S.obj S.property) A).map g) =
      (smallEtaleConstantPullbackIso B A u E).hom ≫
        (constantSheaf (SmallEtale.topology B T.obj T.property) A).map g ≫
          (smallEtaleConstantPullbackIso B A u E').inv := by
  rw [← Category.assoc, Iso.eq_comp_inv]
  exact (smallEtaleSheafPullbackConstantSheafIso B u A).hom.naturality g

end Pullback

section Nonempty

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **The members of a covering with nonempty underlying scheme still cover.** The members with
empty underlying scheme are covered by the empty family
(`AlgebraicGeometry.smallEtaleTopology_bot_mem`), so they can be dropped. -/
public theorem smallEtale_sieve_ofArrows_nonempty_mem {X : SmallEtale B S hS} (R : Sieve X)
    (hR : R ∈ SmallEtale.topology B S hS X) :
    Sieve.ofArrows
        (fun i : (Σ W : SmallEtale B S hS,
          {f : W ⟶ X // R f ∧ Nonempty ((SmallEtale.toScheme B S hS).obj W)}) => i.1)
        (fun i => i.2.1) ∈ SmallEtale.topology B S hS X := by
  refine (SmallEtale.topology B S hS).transitive hR _ (fun W f hf => ?_)
  by_cases hW : Nonempty ((SmallEtale.toScheme B S hS).obj W)
  · refine (SmallEtale.topology B S hS).superset_covering (fun Z k _ => ?_)
      ((SmallEtale.topology B S hS).top_mem W)
    exact (Sieve.ofArrows _ _).downward_closed
      (Sieve.ofArrows_mk _ (fun i : (Σ W : SmallEtale B S hS,
        {f : W ⟶ X // R f ∧ Nonempty ((SmallEtale.toScheme B S hS).obj W)}) => i.2.1)
        ⟨W, f, hf, hW⟩) k
  · exact (SmallEtale.topology B S hS).superset_covering bot_le
      (smallEtaleTopology_bot_mem B S hS (not_nonempty_iff.mp hW))

variable {A : Type w} [Category.{t} A] {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [HasWeakSheafify (SmallEtale.topology B S hS) A]

/-- **Constants are separated over a nonempty étale `S`-scheme.** Over an object of the small
étale site with nonempty underlying scheme, the constant sections of the constant sheaf on `E`
are pairwise distinct: two constants with the same image agree on a covering sieve, and a
geometric point of the object lifts through some member of that sieve, where the restriction of
constants is the identity. -/
public theorem injective_toSheafify_app_const_of_nonempty (E : A)
    [Presheaf.IsLocallyInjective (SmallEtale.topology B S hS)
      (toSheafify (SmallEtale.topology B S hS) ((Functor.const _).obj E))]
    {W : SmallEtale B S hS} (hW : Nonempty ((SmallEtale.toScheme B S hS).obj W)) :
    Function.Injective
      ((toSheafify (SmallEtale.topology B S hS) ((Functor.const _).obj E)).app (op W)) := by
  intro x y hxy
  have hmem := Presheaf.equalizerSieve_mem (SmallEtale.topology B S hS)
    (toSheafify (SmallEtale.topology B S hS) ((Functor.const _).obj E)) x y hxy
  obtain ⟨w⟩ := hW
  let v := GeometricPoint.ofPoint _ w
  let s : GeometricPoint S :=
    { residueField := v.residueField, hom := v.hom ≫ B.inclusion.map W.obj.hom }
  let q : (geometricPointFiber B S hS s).obj W := ⟨v.hom, rfl⟩
  obtain ⟨Y, f, hf, -, -⟩ := (geometricPointSitePoint B S hS s).jointly_surjective _ hmem q
  simpa [Presheaf.equalizerSieve] using hf

/-- **The constant sheaf functor is faithful on a nonempty scheme.** Two maps `g g' : E ⟶ E'`
with the same constant sheaf map agree after composition with the constant section map over the
final object, which is injective because the final object has a point. -/
public theorem smallEtale_constantSheaf_map_injective (hne : Nonempty S) {E E' : A}
    [Presheaf.IsLocallyInjective (SmallEtale.topology B S hS)
      (toSheafify (SmallEtale.topology B S hS) ((Functor.const _).obj E'))]
    {g g' : E ⟶ E'}
    (h : (constantSheaf (SmallEtale.topology B S hS) A).map g =
      (constantSheaf (SmallEtale.topology B S hS) A).map g') : g = g' := by
  have key : ∀ g : E ⟶ E', g ≫ (toSheafify (SmallEtale.topology B S hS)
      ((Functor.const _).obj E')).app (op (SmallEtale.final B S hS)) =
      (toSheafify (SmallEtale.topology B S hS) ((Functor.const _).obj E)).app
        (op (SmallEtale.final B S hS)) ≫
        ((constantSheaf (SmallEtale.topology B S hS) A).map g).hom.app
          (op (SmallEtale.final B S hS)) := fun g =>
    congrArg (fun φ => φ.app (op (SmallEtale.final B S hS)))
      (toSheafify_naturality (SmallEtale.topology B S hS) ((Functor.const _).map g))
  have hinj := injective_toSheafify_app_const_of_nonempty B S hS E'
    (W := SmallEtale.final B S hS) hne
  refine ConcreteCategory.hom_ext _ _ (fun x => hinj ?_)
  have k := ConcreteCategory.congr_hom (key g) x
  have k' := ConcreteCategory.congr_hom (key g') x
  rw [h] at k
  simp only [CategoryTheory.comp_apply] at k k'
  rw [k, k']

end Nonempty

section LocallyConstant

variable (B : BigEtaleSite.{u}) {A : Type t} [Category.{v} A]
  {FA : A → A → Type*} {CA : A → Type*}
  [∀ X Y, FunLike (FA X Y) (CA X) (CA Y)] [ConcreteCategory A FA]
  [∀ (S T : B.Scheme) (f : T ⟶ S),
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous A
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint]
  [∀ (S : B.Scheme), HasWeakSheafify (SmallEtale.topology B S.obj S.property) A]

/-- **Morphisms of constant sheaves are locally constant, for a general concrete coefficient
category.** Let `a` be a morphism from the constant sheaf on `E` to the constant sheaf on `E'` on
the small étale site of `S`, and let `x` be a finite family of elements of `E` such that a map
out of `E` into an object containing `E'` lifts to `E'` as soon as it does so on the `x j`
(`hfac`). Then there is a covering `{V_k → S}` of the final object and maps `g k : E ⟶ E'` such
that the inverse image of `a` to each `V_k` is the constant sheaf map attached to `g k`.

The covering is a common refinement on which the finitely many sections `a(x j)` are constant
(`Stacks.ConstantSheaf.exists_sieve_toSheafify_app_eq`), with its empty members dropped
(`AlgebraicGeometry.smallEtale_sieve_ofArrows_nonempty_mem`); over a nonempty member, constants
are separated (`AlgebraicGeometry.injective_toSheafify_app_const_of_nonempty`), which is where
`hfac` produces `g k`. The passage to inverse images is
`AlgebraicGeometry.smallEtaleSheafPullback_map_eq_of_toSheafify_app_comp_eq`. -/
public theorem exists_cover_smallEtaleSheafPullback_map_eq {S : B.Scheme} {E E' : A}
    [Presheaf.IsLocallySurjective (SmallEtale.topology B S.obj S.property)
      (toSheafify (SmallEtale.topology B S.obj S.property) ((Functor.const _).obj E'))]
    [Presheaf.IsLocallyInjective (SmallEtale.topology B S.obj S.property)
      (toSheafify (SmallEtale.topology B S.obj S.property) ((Functor.const _).obj E'))]
    (a : (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E ⟶
      (constantSheaf (SmallEtale.topology B S.obj S.property) A).obj E')
    {ι : Type*} [Finite ι] (x : ι → ToType E)
    (hfac : ∀ {Q : A} (i : E' ⟶ Q) (φ : E ⟶ Q), Function.Injective i →
      (∀ j, ∃ m, i m = φ (x j)) → ∃ g : E ⟶ E', g ≫ i = φ) :
    ∃ (I : Type (u + 1)) (V : I → SmallEtale B S.obj S.property),
      Sieve.ofArrows V (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from (V k)) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property) ∧
      ∃ g : I → (E ⟶ E'), ∀ k,
        (smallEtaleSheafPullback B A (V k).obj.hom).map a =
          (smallEtaleConstantPullbackIso B A (V k).obj.hom E).hom ≫
            (constantSheaf (SmallEtale.topology B (V k).obj.left.obj (V k).obj.left.property)
              A).map (g k) ≫
            (smallEtaleConstantPullbackIso B A (V k).obj.hom E').inv := by
  obtain ⟨R, hR, hRx⟩ := Stacks.ConstantSheaf.exists_sieve_toSheafify_app_eq
    (SmallEtale.topology B S.obj S.property) a x (SmallEtale.final B S.obj S.property)
  let I := Σ W : SmallEtale B S.obj S.property, {f : W ⟶ SmallEtale.final B S.obj S.property //
    R f ∧ Nonempty ((SmallEtale.toScheme B S.obj S.property).obj W)}
  have hcov := smallEtale_sieve_ofArrows_nonempty_mem B S.obj S.property R hR
  have harr : (fun k : I => k.2.1) =
      fun k : I => (SmallEtale.finalIsTerminal B S.obj S.property).from k.1 :=
    funext fun k => (SmallEtale.finalIsTerminal B S.obj S.property).hom_ext _ _
  have hg : ∀ k : I, ∃ g : E ⟶ E',
      (toSheafify (SmallEtale.topology B S.obj S.property)
          ((Functor.const _).obj E)).app (op k.1) ≫ a.hom.app (op k.1) =
        g ≫ (toSheafify (SmallEtale.topology B S.obj S.property)
          ((Functor.const _).obj E')).app (op k.1) := by
    intro k
    obtain ⟨g, hg⟩ := hfac _ _
      (injective_toSheafify_app_const_of_nonempty B S.obj S.property E' k.2.2.2)
      (fun j => by
        obtain ⟨m, hm⟩ := hRx k.1 k.2.1 k.2.2.1 j
        exact ⟨m, hm.trans (CategoryTheory.comp_apply _ _ _).symm⟩)
    exact ⟨g, hg.symm⟩
  choose g hg using hg
  refine ⟨I, fun k => k.1, ?_, g, fun k : I =>
    smallEtaleSheafPullback_map_eq_of_toSheafify_app_comp_eq B A k.1 a (g k) (hg k)⟩
  rw [← harr]
  exact hcov

end LocallyConstant

section LocallyConstantInstances

variable (B : BigEtaleSite.{u})

/-- Direct image of sheaves of sets along small étale base change is a right adjoint. Stated for
an arbitrary morphism so that it can serve as a local instance: typeclass inference does not
produce the family `∀ S T f, _` that `AlgebraicGeometry.smallEtaleConstantPullbackIso` takes. -/
public theorem SmallEtale.isRightAdjointPushforward_type {S T : B.Scheme} (f : T ⟶ S) :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (Type (u + 1))
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
  inferInstance

/-- Direct image of abelian sheaves along small étale base change is a right adjoint. Stated for
an arbitrary morphism so that it can serve as a local instance, as
`AlgebraicGeometry.SmallEtale.isRightAdjointPushforward_type`. -/
public theorem SmallEtale.isRightAdjointPushforward_addCommGrpCat {S T : B.Scheme}
    (f : T ⟶ S) :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous AddCommGrpCat.{u + 1}
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
  inferInstance

/-- Direct image of sheaves of `Λ`-modules along small étale base change is a right adjoint, at
the coefficient universe of the site. Stated for an arbitrary morphism so that it can serve as a
local instance, as `AlgebraicGeometry.SmallEtale.isRightAdjointPushforward_type`; the
universe-polymorphic `AlgebraicGeometry.SmallEtale.isRightAdjointPushforward_moduleCat` leaves a
universe constraint `u + 1 = max (u + 1) ?w` that unification does not solve. -/
public theorem SmallEtale.isRightAdjointPushforward_moduleCat_site (Λ : Type (u + 1))
    [CommRing Λ] {S T : B.Scheme} (f : T ⟶ S) :
    ((smallEtaleBaseChange B f).sheafPushforwardContinuous (ModuleCat.{u + 1} Λ)
      (SmallEtale.topology B S.obj S.property)
      (SmallEtale.topology B T.obj T.property)).IsRightAdjoint :=
  inferInstance

attribute [local instance] SmallEtale.isRightAdjointPushforward_type
  SmallEtale.isRightAdjointPushforward_addCommGrpCat
  SmallEtale.isRightAdjointPushforward_moduleCat_site

variable (S : B.Scheme)

/-- **Morphisms of constant sheaves of sets with finite source are locally constant.** A morphism
from the constant sheaf on a finite set `E` to the constant sheaf on `E'` on the small étale site
of `S` is, after inverse image to the members of an étale covering of `S`, the constant sheaf map
attached to a map `E ⟶ E'`. -/
public theorem exists_cover_smallEtaleSheafPullback_map_eq_type {E E' : Type (u + 1)}
    [Finite E]
    (a : (constantSheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))).obj E ⟶
      (constantSheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))).obj E') :
    ∃ (I : Type (u + 1)) (V : I → SmallEtale B S.obj S.property),
      Sieve.ofArrows V (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from (V k)) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property) ∧
      ∃ g : I → (E ⟶ E'), ∀ k,
        (smallEtaleSheafPullback B (Type (u + 1)) (V k).obj.hom).map a =
          (smallEtaleConstantPullbackIso B (Type (u + 1)) (V k).obj.hom E).hom ≫
            (constantSheaf (SmallEtale.topology B (V k).obj.left.obj (V k).obj.left.property)
              (Type (u + 1))).map (g k) ≫
            (smallEtaleConstantPullbackIso B (Type (u + 1)) (V k).obj.hom E').inv := by
  refine exists_cover_smallEtaleSheafPullback_map_eq B a (ι := E) id ?_
  intro Q i φ _ hφ
  choose m hm using hφ
  exact ⟨TypeCat.ofHom m, by ext e; exact hm e⟩

/-- **Morphisms of constant abelian sheaves with finite source are locally constant.** A
morphism from the constant sheaf on a finite abelian group `E` to the constant sheaf on `E'` on
the small étale site of `S` is, after inverse image to the members of an étale covering of `S`,
the constant sheaf map attached to a homomorphism `E ⟶ E'`. -/
public theorem exists_cover_smallEtaleSheafPullback_map_eq_addCommGrpCat
    {E E' : AddCommGrpCat.{u + 1}} [Finite E]
    (a : (constantSheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}).obj E ⟶
      (constantSheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}).obj E') :
    ∃ (I : Type (u + 1)) (V : I → SmallEtale B S.obj S.property),
      Sieve.ofArrows V (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from (V k)) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property) ∧
      ∃ g : I → (E ⟶ E'), ∀ k,
        (smallEtaleSheafPullback B AddCommGrpCat.{u + 1} (V k).obj.hom).map a =
          (smallEtaleConstantPullbackIso B AddCommGrpCat.{u + 1} (V k).obj.hom E).hom ≫
            (constantSheaf (SmallEtale.topology B (V k).obj.left.obj (V k).obj.left.property)
              AddCommGrpCat.{u + 1}).map (g k) ≫
            (smallEtaleConstantPullbackIso B AddCommGrpCat.{u + 1} (V k).obj.hom E').inv := by
  refine exists_cover_smallEtaleSheafPullback_map_eq B a (ι := E) id ?_
  intro Q i φ hi hφ
  choose m hm using hφ
  simp only [id] at hm
  refine ⟨AddCommGrpCat.ofHom
    { toFun := m
      map_zero' := hi (by rw [hm, map_zero, map_zero])
      map_add' := fun x y => hi (by rw [map_add, hm, hm, hm, map_add]) }, ?_⟩
  ext e
  exact hm e

/-- **Morphisms of constant sheaves of modules with finitely generated source are locally
constant.** A morphism from the constant sheaf on a finitely generated `Λ`-module `E` to the
constant sheaf on `E'` on the small étale site of `S` is, after inverse image to the members of
an étale covering of `S`, the constant sheaf map attached to a linear map `E ⟶ E'`. No finite
presentation is needed: over a nonempty étale `S`-scheme constants are separated. -/
public theorem exists_cover_smallEtaleSheafPullback_map_eq_moduleCat (Λ : Type (u + 1))
    [CommRing Λ] {E E' : ModuleCat.{u + 1} Λ} [Module.Finite Λ E]
    (a : (constantSheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ)).obj E ⟶
      (constantSheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ)).obj E') :
    ∃ (I : Type (u + 1)) (V : I → SmallEtale B S.obj S.property),
      Sieve.ofArrows V (fun k => (SmallEtale.finalIsTerminal B S.obj S.property).from (V k)) ∈
        SmallEtale.topology B S.obj S.property (SmallEtale.final B S.obj S.property) ∧
      ∃ g : I → (E ⟶ E'), ∀ k,
        (smallEtaleSheafPullback B (ModuleCat.{u + 1} Λ) (V k).obj.hom).map a =
          (smallEtaleConstantPullbackIso B (ModuleCat.{u + 1} Λ) (V k).obj.hom E).hom ≫
            (constantSheaf (SmallEtale.topology B (V k).obj.left.obj (V k).obj.left.property)
              (ModuleCat.{u + 1} Λ)).map (g k) ≫
            (smallEtaleConstantPullbackIso B (ModuleCat.{u + 1} Λ) (V k).obj.hom E').inv := by
  obtain ⟨s, hs⟩ := (Module.Finite.fg_top : (⊤ : Submodule Λ E).FG)
  refine exists_cover_smallEtaleSheafPullback_map_eq B a (ι := s) Subtype.val ?_
  intro Q i φ hi hφ
  have hle : LinearMap.range φ.hom ≤ LinearMap.range i.hom := by
    rw [LinearMap.range_eq_map, ← hs, Submodule.map_span, Submodule.span_le]
    rintro _ ⟨e, he, rfl⟩
    exact hφ ⟨e, he⟩
  let ψ := (LinearEquiv.ofInjective i.hom hi).symm.toLinearMap ∘ₗ
    φ.hom.codRestrict (LinearMap.range i.hom) (fun e => hle ⟨e, rfl⟩)
  refine ⟨ModuleCat.ofHom ψ, ?_⟩
  ext e
  have h1 := LinearEquiv.ofInjective_apply (f := i.hom) (h := hi) (ψ e)
  rw [show LinearEquiv.ofInjective i.hom hi (ψ e) = ⟨φ.hom e, hle ⟨e, rfl⟩⟩ from
    LinearEquiv.apply_symm_apply _ _] at h1
  exact h1.symm

end LocallyConstantInstances

section Faithful

variable (B : BigEtaleSite.{u}) (S : B.Scheme)

/-- **Faithfulness of constant sheaves of sets on a nonempty scheme.** -/
public theorem smallEtale_constantSheaf_map_injective_type (hne : Nonempty S.obj)
    {E E' : Type (u + 1)} {g g' : E ⟶ E'}
    (h : (constantSheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))).map g =
      (constantSheaf (SmallEtale.topology B S.obj S.property) (Type (u + 1))).map g') :
    g = g' :=
  smallEtale_constantSheaf_map_injective B S.obj S.property hne h

/-- **Faithfulness of constant sheaves of abelian groups on a nonempty scheme.** -/
public theorem smallEtale_constantSheaf_map_injective_addCommGrpCat (hne : Nonempty S.obj)
    {E E' : AddCommGrpCat.{u + 1}} {g g' : E ⟶ E'}
    (h : (constantSheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}).map g =
      (constantSheaf (SmallEtale.topology B S.obj S.property) AddCommGrpCat.{u + 1}).map g') :
    g = g' :=
  smallEtale_constantSheaf_map_injective B S.obj S.property hne h

/-- **Faithfulness of constant sheaves of modules on a nonempty scheme.** -/
public theorem smallEtale_constantSheaf_map_injective_moduleCat (hne : Nonempty S.obj)
    (Λ : Type (u + 1)) [CommRing Λ] {E E' : ModuleCat.{u + 1} Λ} {g g' : E ⟶ E'}
    (h : (constantSheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ)).map g =
      (constantSheaf (SmallEtale.topology B S.obj S.property) (ModuleCat.{u + 1} Λ)).map g') :
    g = g' :=
  smallEtale_constantSheaf_map_injective B S.obj S.property hne h

end Faithful

end AlgebraicGeometry

end
