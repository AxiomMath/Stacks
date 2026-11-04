module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.KilledSubsheafSystem
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CohomologicalDimension.Gabber.ZariskiRiemann.RefinementKillsComp
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.DerivedGeometricStalkSections
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.SmallEtaleAbelianStalkBaseChange
public import StacksFrontier.CategoryTheory.Sites.FreeRepresentableSheafULift
public import Mathlib.Algebra.Category.Grp.AB
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Colim
public import Mathlib.CategoryTheory.Abelian.GrothendieckAxioms.Sheaf
public import Mathlib.CategoryTheory.Subobject.Limits

/-!
# The killed-subsheaf system from germs killed by refinements

Travaux de Gabber, Exposé XVIII-A, last remark of §2, passes to the limit over the proper models
of `η = Spec (Frac B)`. At one model `M` with `G = R^q j_* F`, the finite-level form of that limit
(`AlgebraicGeometry.Scheme.ZariskiRiemann.KilledSubsheafSystemBound`) asks for a filtered system
of subsheaves of `G`, each killed by a refinement of `M`, whose cokernel restricted to the
geometric closed fibre `Y_Ω` is supported in transcendence degree `≤ min(e - 1, e - q)`.

This file builds that system from a pointwise statement, `GermKilling`: every section `g` of `G`
over an étale `V ⟶ Y` dies, after restriction to finitely many étale `V_k ⟶ V`, on refinements of
`M`, and the `V_k ×_Y Y_Ω` cover every point of `V ×_Y Y_Ω` lying over a point of `Y_Ω` of large
transcendence degree. In the source this is the stalk computation through valuation rings: the
stalk of the limit sheaf `A_q` at such a point is `H^q(Frac V^{sh}, F) = 0`.

The system is the source's: the index category is the set of finite sets `T` of *killed germs*
`(V, g)` (sections whose morphism `ℤ_V ⟶ G` from the free abelian sheaf is killed by some
refinement), and `K_T ⊆ G` is the image of `∐_{t ∈ T} ℤ_{V_t} ⟶ G`. Then:

* `K_T` is killed by one refinement, because finitely many killed morphisms have a common killing
  refinement
  (`AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.exists_refinement_kills_image_sigmaDesc`,
  which needs killing to be stable under refinement and refinements to be cofiltered);
* `colim K_T ⟶ G` is a monomorphism, sheaves of abelian groups satisfying AB5;
* the stalk of the cokernel vanishes at every geometric point of `Y_Ω` over a point of large
  transcendence degree: a germ of `G` there is the germ of some `g` over an étale neighbourhood
  `V`; `GermKilling` gives a `V_k ⟶ V` through which the point lifts (étale maps lift geometric
  points), and `g|V_k` lies in `K_{(V_k, g|V_k)}`.

## Main definitions

* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.germHom` — the morphism `ℤ_V ⟶ G` of a
  section `g ∈ G(V)`.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.GermKilling` — the pointwise germ-killing statement.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.KilledGerm` and
  `AlgebraicGeometry.Scheme.ZariskiRiemann.ProperModel.killedGermDiagram` — the killed germs and
  the system of subsheaves `K_T` they generate.

## Main results

* `Stacks.EtaleCohomology.mono_colimitDesc_of_forall_mono` — a filtered system of subobjects in an
  AB5 category has monomorphic colimit map.
* `Stacks.EtaleCohomology.isZero_smallEtaleStalkAb_cokernel_of_forall_germ` — the stalk of a
  cokernel vanishes when every germ of the target lifts.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.killedSubsheafSystemBound_of_germKilling` —
  `KilledSubsheafSystemBound n` from `GermKilling n`, given that refinements of proper models are
  cofiltered.
* `AlgebraicGeometry.Scheme.ZariskiRiemann.zariskiRiemannKilling_of_germKilling` — hence
  `ZariskiRiemannKilling n`.

## References

* Travaux de Gabber sur l'uniformisation locale et la cohomologie étale des schémas
  quasi-excellents, Exposé XVIII-A (L. Illusie), last remark of §2, Astérisque 363–364 (2014)
* SGA 4, Exposé VI, 8.7.4
* [Stacks Project, Tag 03PT](https://stacks.math.columbia.edu/tag/03PT)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits CategoryTheory.GrothendieckTopology Opposite
open AlgebraicGeometry AlgebraicGeometry.Scheme

universe v u₁ u

namespace Stacks.EtaleCohomology

/-- **A filtered system of subobjects has monomorphic colimit map** in a category where filtered
colimits preserve monomorphisms (e.g. an AB5 category): `colimit.desc` is `colim` of the
monomorphism `K ⟶ const G`, followed by the identification of the colimit of a constant diagram
over a connected category. -/
theorem mono_colimitDesc_of_forall_mono {C : Type u₁} [Category.{v} C] {I : Type v}
    [SmallCategory I] [IsFiltered I] [HasColimitsOfShape I C]
    [(colim : (I ⥤ C) ⥤ C).PreservesMonomorphisms] (K : I ⥤ C) {G : C}
    (ι : K ⟶ (Functor.const I).obj G) [∀ i, Mono (ι.app i)] :
    Mono (colimit.desc K (Cocone.mk G ι)) := by
  have := NatTrans.mono_of_mono_app ι
  have : IsConnected I := IsFiltered.isConnected I
  exact colim.map_mono' ι (colimit.isColimit K) (isColimitConstCocone I G) _
    (fun j ↦ (colimit.ι_desc (Cocone.mk G ι) j).trans (Category.comp_id _).symm)

private instance forgetAddCommGrpCatPreservesFilteredColimitsOfSize :
    PreservesFilteredColimitsOfSize.{u, u} (forget AddCommGrpCat.{u + 1}) :=
  preservesFilteredColimitsOfSize_of_univLE.{u + 1, u + 1, u, u} (forget AddCommGrpCat.{u + 1})

/-- **The stalk of a cokernel vanishes when every germ of the target lifts.** Let `d : K ⟶ G` be a
morphism of abelian sheaves on `Y_étale` and `t` a geometric point. If every section `g` of `G`
over an étale neighbourhood `(V, ℓ)` of `t` becomes, on some smaller étale neighbourhood
`(W, ℓ')`, the image under `d` of a section of `K`, the stalk at `t` of `cokernel d` vanishes:
the stalk of `d` is surjective, and the stalk functor preserves cokernels. -/
theorem isZero_smallEtaleStalkAb_cokernel_of_forall_germ {Y : Scheme.{u}} {Ω : Type u} [Field Ω]
    [IsSepClosed Ω] (t : Spec (.of Ω) ⟶ Y)
    {K G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}} (d : K ⟶ G)
    (h : ∀ (V : Y.Etale) (ℓ : (Scheme.pointSmallEtale t).fiber.obj V) (g : G.obj.obj (op V)),
      ∃ (W : Y.Etale) (f : W ⟶ V) (ℓ' : (Scheme.pointSmallEtale t).fiber.obj W)
        (w : K.obj.obj (op W)),
        (Scheme.pointSmallEtale t).fiber.map f ℓ' = ℓ ∧ d.hom.app (op W) w = G.obj.map f.op g) :
    IsZero ((smallEtaleStalkAb t).obj (cokernel d)) := by
  have hepi : Epi ((smallEtaleStalkAb t).map d) := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro p
    obtain ⟨V, ℓ, g, rfl⟩ :=
      (Scheme.pointSmallEtale t).toPresheafFiber_jointly_surjective (P := G.obj) p
    obtain ⟨W, f, ℓ', w, rfl, hw⟩ := h V ℓ g
    refine ⟨(Scheme.pointSmallEtale t).toPresheafFiber W ℓ' K.obj w, ?_⟩
    change (Scheme.pointSmallEtale t).presheafFiber.map d.hom _ = _
    rw [Point.toPresheafFiber_naturality_apply, hw, Point.toPresheafFiber_w_apply]
  exact (isZero_cokernel_of_epi ((smallEtaleStalkAb t).map d)).of_iso
    (PreservesCokernel.iso (smallEtaleStalkAb t) d)

/-- **Stalks of an inverse image vanish where the stalks of the sheaf do.** For `π : X' ⟶ X` and a
geometric point `s` of `X'`, the stalk of `π⁻¹ Q` at `s` is the stalk of `Q` at `s ≫ π`. -/
theorem isZero_smallEtaleStalkAb_etaleAbelianInverseImage {X X' : Scheme.{u}} (π : X' ⟶ X)
    {Ω : Type u} [Field Ω] [IsSepClosed Ω] (s : Spec (.of Ω) ⟶ X')
    (Q : Sheaf X.smallEtaleTopology AddCommGrpCat.{u + 1})
    (hQ : IsZero ((smallEtaleStalkAb (s ≫ π)).obj Q)) :
    IsZero ((smallEtaleStalkAb s).obj ((etaleAbelianInverseImage.{u, 0} π).obj Q)) :=
  hQ.of_iso (((smallEtaleStalkAb s).mapIso
    ((smallEtalePullbackAbIsoEtaleAbelianInverseImage π).app Q)).symm ≪≫
      (smallEtaleStalkPullbackAbIso π s).app Q)

end Stacks.EtaleCohomology

namespace AlgebraicGeometry.Scheme.ZariskiRiemann

attribute [local instance high]
  Stacks.EtaleCohomology.ConstantTransport.hasExt_sheaf_smallEtaleTopology

open Stacks.EtaleCohomology Stacks.Sites.FreeRepresentable

namespace ProperModel

/-- **The morphism `ℤ_V ⟶ G` of a section.** For an abelian sheaf `G` on `Y_étale`, an étale
`V ⟶ Y` and `g ∈ G(V)`, the morphism from the free abelian sheaf on `V` sending the generator to
`g`. -/
abbrev germHom {Y : Scheme.{u}} {G : Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}}
    (V : Y.Etale) (g : G.obj.obj (op V)) :
    freeRepULift.{u + 1} Y.smallEtaleTopology V ⟶ G :=
  (freeRepULiftEquiv Y.smallEtaleTopology V G).symm g

end ProperModel

/-- **Germs of `R^q j_* F` die on refinements, away from small transcendence degree.** For `B` a
strictly henselian Noetherian local domain of dimension `e ≥ 1` with `n` invertible, `F` killed by
`n` on `η = Spec (Frac B)`, a proper model `M` and a degree `q`, there is a geometric point
`x : Spec Ω ⟶ Spec B` over the closed point such that for every étale `V ⟶ Y` and every section
`g` of `R^q j_* F` over `V` there are finitely many étale `V_k ⟶ V`, each with a refinement of
`M` killing the morphism `ℤ_{V_k} ⟶ R^q j_* F` of `g|V_k`, such that the images of the
`V_k ×_Y Y_Ω` cover every point of `V ×_Y Y_Ω` whose image `y ∈ Y_Ω` lies in no
`E_a = {trdeg_Ω κ(y) ≤ a}` with `a + q ≤ e` and `a + 1 ≤ e`.

In the source this is the computation of the stalks of the limit sheaf `A_q` on the
Zariski–Riemann space: at a valuation ring `V` of `Frac B` centred at `y`, the stalk is
`H^q(Frac V^{sh}, F)`, which vanishes when `trdeg κ(V) > e - q` (Abhyankar's inequality and
`cd(Frac V^{sh}) ≤ rat.rank Γ_V`); since `κ(y) ⊆ κ(V)`, every such `V` centred at a point `y`
with `trdeg κ(y) > e - q` has a vanishing stalk, and by quasi-compactness of the
Zariski–Riemann fibre over `y` and properness of the models, finitely many étale neighbourhoods
and one common refinement suffice. (The closed fibre has dimension `≤ e - 1`, so the condition
`a + 1 ≤ e` holds at every point of `Y_Ω`; it records `δ ≤ e - 1`.) -/
def GermKilling (n : ℕ) : Prop :=
  ∀ (B : Type u) [CommRing B] [IsDomain B] [IsNoetherianRing B] [StrictlyHenselianLocalRing B]
    (e : ℕ), ringKrullDim B = e → 0 < e → IsUnit (n : B) →
    ∀ (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}),
      (∀ (T : (Spec (.of (FractionRing B))).Etale) (s : F.obj.obj (op T)), n • s = 0) →
      ∀ (M : ProperModel B) (q : ℕ),
        ∃ (Ω : Type u) (_ : Field Ω) (_ : IsAlgClosed Ω) (x : Spec (.of Ω) ⟶ Spec (.of B)),
          x (default : Spec (.of Ω)) = IsLocalRing.closedPoint B ∧
          ∀ (V : M.Y.Etale)
            (g : (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj (op V)),
            ∃ (m : ℕ) (W : Fin m → M.Y.Etale) (h : ∀ k, W k ⟶ V),
              (∀ k, ∃ (M' : ProperModel B) (φ : ProperModel.Refinement M' M),
                φ.Kills F q (ProperModel.germHom (W k)
                  ((((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.map
                    (h k).op g))) ∧
              ∀ z : ↥(pullback V.hom (pullback.fst M.f x)),
                (¬ ∃ a : ℕ, a + q ≤ e ∧ a + 1 ≤ e ∧
                    pullback.snd V.hom (pullback.fst M.f x) z ∈
                      Scheme.trdegLESet Ω (pullback.snd M.f x) a) →
                ∃ (k : Fin m) (z' : ↥(pullback (W k).hom (pullback.fst M.f x))),
                  pullback.map (W k).hom (pullback.fst M.f x) V.hom (pullback.fst M.f x)
                    (h k).left (𝟙 _) (𝟙 _)
                    (by rw [Category.comp_id]; exact (MorphismProperty.Over.w (h k)).symm)
                    (by simp) z' = z

namespace ProperModel

/-- Finite coproducts of abelian sheaves on a small étale site, as an instance of high priority:
the generic search for `HasColimit (Discrete.functor _)` in these categories times out. -/
instance (priority := high) hasColimit_discrete_smallEtale {Y : Scheme.{u}} {ι : Type (u + 1)}
    [Finite ι] (K : ι → Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) :
    HasColimit (Discrete.functor K) :=
  haveI := hasColimitsOfShape_discrete (Sheaf Y.smallEtaleTopology AddCommGrpCat.{u + 1}) ι
  HasColimitsOfShape.has_colimit _

variable {B : Type u} [CommRing B] [IsDomain B] (M : ProperModel B)
  (F : Sheaf (Spec (.of (FractionRing B))).smallEtaleTopology AddCommGrpCat.{u + 1}) (q : ℕ)

/-- A **killed germ**: an étale `V ⟶ Y` with a section `g` of `R^q j_* F` over `V` whose morphism
`ℤ_V ⟶ R^q j_* F` is killed by some refinement of `M`. -/
abbrev KilledGerm : Type (u + 1) :=
  {p : Σ V : M.Y.Etale, (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F).obj.obj
      (op V) //
    ∃ (M' : ProperModel B) (φ : Refinement M' M), φ.Kills F q (germHom p.1 p.2)}

variable {M F q}

/-- The morphism `∐_{t ∈ T} ℤ_{V_t} ⟶ R^q j_* F` of a finite set `T` of killed germs. -/
def killedGermSigmaDesc (T : Finset (KilledGerm M F q)) :
    (∐ fun t : T ↦ freeRepULift.{u + 1} M.Y.smallEtaleTopology t.1.1.1) ⟶
      ((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F :=
  Sigma.desc fun t ↦ germHom t.1.1.1 t.1.1.2

/-- The subsheaf `K_T ⊆ R^q j_* F` generated by a finite set `T` of killed germs: the image of
`∐_{t ∈ T} ℤ_{V_t} ⟶ R^q j_* F`. -/
def killedGermSubobject (T : Finset (KilledGerm M F q)) :
    Subobject (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) :=
  imageSubobject (killedGermSigmaDesc T)

omit [IsDomain B] in
/-- The subsheaf generated by killed germs grows with the set of germs. -/
theorem killedGermSubobject_monotone :
    Monotone (killedGermSubobject (M := M) (F := F) (q := q)) := by
  intro T T' hT
  let incl : (∐ fun t : T ↦ freeRepULift.{u + 1} M.Y.smallEtaleTopology t.1.1.1) ⟶
      (∐ fun t : T' ↦ freeRepULift.{u + 1} M.Y.smallEtaleTopology t.1.1.1) :=
    Sigma.desc fun t ↦ Sigma.ι (fun t : T' ↦ freeRepULift.{u + 1} M.Y.smallEtaleTopology t.1.1.1)
      ⟨t.1, hT t.2⟩
  have heq : incl ≫ killedGermSigmaDesc T' = killedGermSigmaDesc T := by
    refine Sigma.hom_ext _ _ fun t ↦ ?_
    simp [incl, killedGermSigmaDesc]
  have hle := imageSubobject_comp_le incl (killedGermSigmaDesc T')
  rw [heq] at hle
  exact hle

variable (M F q)

/-- **The system of killed subsheaves**: `T ↦ K_T` over the finite sets of killed germs. -/
def killedGermDiagram :
    Finset (KilledGerm M F q) ⥤ Sheaf M.Y.smallEtaleTopology AddCommGrpCat.{u + 1} :=
  killedGermSubobject_monotone.functor ⋙ Subobject.underlying

/-- The inclusions `K_T ⟶ R^q j_* F`. -/
def killedGermι :
    killedGermDiagram M F q ⟶
      (Functor.const _).obj (((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F) where
  app T := (killedGermSubobject T).arrow
  naturality T T' f := by
    simp [killedGermDiagram]

instance (T : Finset (KilledGerm M F q)) : Mono ((killedGermι M F q).app T) := by
  dsimp [killedGermι]
  exact Subobject.arrow_mono _

/-- **Each `K_T` is killed by one refinement**, given that refinements are cofiltered (killing is
stable under refinement by `AlgebraicGeometry.Scheme.ZariskiRiemann.killsStableUnderRefinement`). -/
theorem exists_refinement_kills_killedGermι (hcof : RefinementsCofiltered B)
    (T : Finset (KilledGerm M F q)) :
    ∃ (M' : ProperModel B) (φ : Refinement M' M), φ.Kills F q ((killedGermι M F q).app T) := by
  obtain ⟨M', φ, hφ⟩ := exists_refinement_kills_image_sigmaDesc F q killsStableUnderRefinement
    hcof M (fun t : T ↦ germHom t.1.1.1 t.1.1.2) (fun t ↦ t.1.2)
  refine ⟨M', φ, ?_⟩
  have h := Refinement.Kills.comp_left (imageSubobjectIso (killedGermSigmaDesc T)).hom hφ
  dsimp [killedGermι, killedGermSubobject]
  rw [← imageSubobject_arrow]
  exact h

omit [IsDomain B] in
/-- **The colimit of the killed subsheaves maps monomorphically to `R^q j_* F`**: abelian sheaves
satisfy AB5. -/
theorem mono_colimitDesc_killedGermDiagram :
    Mono (colimit.desc (killedGermDiagram M F q) (Cocone.mk _ (killedGermι M F q))) := by
  classical
  exact mono_colimitDesc_of_forall_mono _ _

omit [IsDomain B] in
/-- **A killed germ lies in the colimit.** For a killed germ `(W, g)`, the section `g` of
`R^q j_* F` over `W` is the image of a section of `colim K_T`. -/
theorem exists_colimitDesc_killedGermDiagram_eq (t : KilledGerm M F q) :
    ∃ w : (colimit (killedGermDiagram M F q)).obj.obj (op t.1.1),
      (colimit.desc (killedGermDiagram M F q) (Cocone.mk _ (killedGermι M F q))).hom.app
        (op t.1.1) w = t.1.2 := by
  classical
  let ι₀ := Sigma.ι (fun s : ({t} : Finset _) ↦
      freeRepULift.{u + 1} M.Y.smallEtaleTopology s.1.1.1) ⟨t, Finset.mem_singleton_self t⟩ ≫
    factorThruImageSubobject (killedGermSigmaDesc {t})
  have hcomp : ι₀ ≫ (imageSubobject (killedGermSigmaDesc {t})).arrow = germHom t.1.1 t.1.2 := by
    rw [Category.assoc, imageSubobject_arrow_comp]
    simp [killedGermSigmaDesc]
  let w₀ : ((killedGermDiagram M F q).obj {t}).obj.obj (op t.1.1) :=
    ι₀.hom.app (op t.1.1) (freeRepULiftGen M.Y.smallEtaleTopology t.1.1)
  refine ⟨(colimit.ι (killedGermDiagram M F q) {t}).hom.app (op t.1.1) w₀, ?_⟩
  have h1 := congrArg (fun φ ↦ φ.hom.app (op t.1.1) w₀)
    (colimit.ι_desc (Cocone.mk _ (killedGermι M F q)) {t})
  have h2 := congrArg (fun φ ↦ φ.hom.app (op t.1.1) (freeRepULiftGen M.Y.smallEtaleTopology t.1.1))
    hcomp
  simp only [ObjectProperty.FullSubcategory.comp_hom, NatTrans.comp_app,
    ConcreteCategory.comp_apply] at h1 h2
  exact h1.trans (h2.trans (freeRepULiftEquiv_symm_app_gen _ _ _))

end ProperModel

/-- **The killed-subsheaf system from germ killing.** If refinements of proper models are
cofiltered, `GermKilling n` gives `KilledSubsheafSystemBound n` (killing is stable under refinement
by `AlgebraicGeometry.Scheme.ZariskiRiemann.killsStableUnderRefinement`): the system of
subsheaves of `R^q j_* F` generated by finite sets of killed germs is filtered, each is killed by
one refinement, its colimit maps monomorphically to `R^q j_* F`, and the stalks of the cokernel on
`Y_Ω` vanish over the points of large transcendence degree. -/
theorem killedSubsheafSystemBound_of_germKilling {n : ℕ}
    (hcof : ∀ (B : Type u) [CommRing B] [IsDomain B], RefinementsCofiltered B)
    (hgerm : GermKilling.{u} n) : KilledSubsheafSystemBound.{u} n := by
  classical
  intro B _ _ _ _ e he he0 hn F hF M q
  obtain ⟨Ω, _, _, x, hx, hcov⟩ := hgerm B e he he0 hn F hF M q
  refine ⟨Finset (ProperModel.KilledGerm M F q), inferInstance, inferInstance,
    ProperModel.killedGermDiagram M F q, ProperModel.killedGermι M F q,
    ProperModel.exists_refinement_kills_killedGermι M F q (hcof B),
    ProperModel.mono_colimitDesc_killedGermDiagram M F q, Ω, inferInstance, inferInstance, x, hx,
    ?_⟩
  set G := ((etaleAbelianDirectImage.{u, 0} M.j).rightDerived q).obj F
  intro y hy
  by_contra hbad
  obtain ⟨s, hs, hnz⟩ := hy
  apply hnz
  apply isZero_smallEtaleStalkAb_etaleAbelianInverseImage
  apply isZero_smallEtaleStalkAb_cokernel_of_forall_germ
  intro V ℓ g
  obtain ⟨m, W, h, hkill, hcov'⟩ := hcov V g
  have hℓ : ℓ.left ≫ V.hom = s.hom ≫ pullback.fst M.f x := Over.w ℓ
  let z₀ : Spec (.of s.residueField) ⟶ pullback V.hom (pullback.fst M.f x) :=
    pullback.lift ℓ.left s.hom hℓ
  have hz₀snd : z₀ ≫ pullback.snd V.hom (pullback.fst M.f x) = s.hom := pullback.lift_snd _ _ _
  have hz₀fst : z₀ ≫ pullback.fst V.hom (pullback.fst M.f x) = ℓ.left := pullback.lift_fst _ _ _
  obtain ⟨k, z', hz'⟩ := hcov' (z₀ (default : Spec (.of s.residueField))) (by
    rintro ⟨a, ha1, ha2, ha3⟩
    apply hbad
    refine ⟨a, ha1, ha2, ?_⟩
    have hsnd : pullback.snd V.hom (pullback.fst M.f x) (z₀ default) = s.hom default := by
      rw [← Scheme.Hom.comp_apply, hz₀snd]
    rw [hsnd, hs] at ha3
    exact ha3)
  let pm := pullback.map (W k).hom (pullback.fst M.f x) V.hom (pullback.fst M.f x)
    (h k).left (𝟙 _) (𝟙 _) (by rw [Category.comp_id]; exact (MorphismProperty.Over.w (h k)).symm)
    (by simp)
  have hpm : Etale pm :=
    MorphismProperty.pullbackMap (P := @Etale) (inferInstance : Etale (h k).left)
      (inferInstance : Etale (𝟙 (pullback M.f x))) (MorphismProperty.Over.w (h k)).symm
      (Category.id_comp _).symm
  obtain ⟨l, hl, -⟩ := Scheme.exists_fac_of_etale_of_isSepClosed pm z₀ z' hz'
  have hlsnd : l ≫ pullback.snd (W k).hom (pullback.fst M.f x) = s.hom := by
    have := congrArg (· ≫ pullback.snd V.hom (pullback.fst M.f x)) hl
    simpa [pm, hz₀snd] using this
  have hlfst : l ≫ pullback.fst (W k).hom (pullback.fst M.f x) ≫ (h k).left = ℓ.left := by
    have := congrArg (· ≫ pullback.fst V.hom (pullback.fst M.f x)) hl
    simpa [pm, hz₀fst] using this
  let t₀ : ProperModel.KilledGerm M F q := ⟨⟨W k, G.obj.map (h k).op g⟩, hkill k⟩
  obtain ⟨w, hw⟩ := ProperModel.exists_colimitDesc_killedGermDiagram_eq M F q t₀
  refine ⟨W k, h k, Over.homMk (l ≫ pullback.fst _ _) ?_, w, ?_, hw⟩
  · simp [pullback.condition, reassoc_of% hlsnd]
  · change Over.homMk _ _ ≫ (Etale.forget _).map (h k) = ℓ
    exact Over.OverMorphism.ext ((Category.assoc _ _ _).trans hlfst)

/-- **The geometric half of the Zariski–Riemann limit step from germ killing**: if refinements of
proper models are cofiltered, `GermKilling n` gives `ZariskiRiemannKilling n`. -/
theorem zariskiRiemannKilling_of_germKilling {n : ℕ}
    (hcof : ∀ (B : Type u) [CommRing B] [IsDomain B], RefinementsCofiltered B)
    (hgerm : GermKilling.{u} n) : ZariskiRiemannKilling.{u} n :=
  zariskiRiemannKilling_of_killedSubsheafSystemBound
    (killedSubsheafSystemBound_of_germKilling hcof hgerm)

end AlgebraicGeometry.Scheme.ZariskiRiemann

end
