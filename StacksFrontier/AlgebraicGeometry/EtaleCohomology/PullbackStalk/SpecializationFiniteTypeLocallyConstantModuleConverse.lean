module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Algebra.Category.ModuleCat.FilteredColimitFinitePresentation
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ConcreteBijectiveGerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.SpecializationFiniteTypeLocallyConstantModule
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves

/-!
# Finite type locally constant sheaves of modules via stalks and specialization maps

Let `S` be a scheme every quasi-compact open of which has finitely many irreducible components,
let `Λ` be a Noetherian ring and let `F` be a sheaf of `Λ`-modules on the small étale site of
`S`. Then `F` is locally constant of finite type precisely when all its stalks at geometric
points are finitely generated `Λ`-modules and all specialization maps between those stalks are
bijective (Tag 0GKC). This is the module-coefficient analogue of Tag 0GJ7.

The implication (1) ⟹ (2) is
`AlgebraicGeometry.isFG_etaleStalk_of_isFiniteTypeLocallyConstantModuleSheaf` together with
`AlgebraicGeometry.bijective_specializationMapOnStalks_of_isFiniteTypeLocallyConstantModuleSheaf`.
This file proves the converse and assembles the equivalence.

For the converse, a finitely generated stalk is finitely presented because `Λ` is Noetherian, so
the identity map of the stalk factors through the sections over one étale neighbourhood; the
resulting map of `Λ`-modules into the sections induces the identity on the stalk at the point.
The locus where the induced germ maps are bijective is stable under specialization and
generalization, because the germ maps at a point and at a generization of it differ by a
specialization map on stalks, hence it is open; and on the open subscheme it cuts out the sheaf
is comparable to the constant sheaf on the stalk by a locally bijective map.

## Main results

* `AlgebraicGeometry.exists_moduleHom_representing_isFG_etaleStalk` — a finitely generated stalk
  is represented by a map of `Λ`-modules into the sections over one étale neighbourhood.
* `AlgebraicGeometry.isFiniteTypeLocallyConstantModuleSheaf_of_isFG_etaleStalk` — the
  implication (2) ⟹ (1) of Tag 0GKC.
* `AlgebraicGeometry.isFiniteTypeLocallyConstantModuleSheaf_iff_isFG_etaleStalk_and_bijective`
  — Tag 0GKC.

## Implementation notes

"Finite `Λ`-module" is read as "finitely generated `Λ`-module", which is the source's meaning of
*finite module*; it is `ModuleCat.isFG`, not finiteness of the underlying set.

The ring `Λ` lives in an arbitrary universe `r` and the sheaves take values in
`ModuleCat.{max (u + 1) r} Λ`, the smallest module universe containing both `Λ` and the small
étale site, whose objects live in `Type (u + 1)`. This is the coefficient universe of the
implication (1) ⟹ (2) already in the library, and the source imposes no universe restriction.

The factorization of the identity of a finitely presented stalk through a stage of the colimit
of sections is `Module.FinitePresentation.exists_comp_eq_of_isColimit`. In the converse the
covering of an object `U` of the small étale site is indexed by the pairs of a geometric point
of `S` and a lift of it to `U`; finiteness of the irreducible components of quasi-compact opens
passes from `S` to the common étale neighbourhood by Tag 0BAL
(`AlgebraicGeometry.finiteIrreducibleComponents_of_etale`), which is what makes the locus of
bijectivity open. The hypothesis on `S` is the tag's own and is not strengthened to a Noetherian
hypothesis.

## References

* [Stacks Project, Tag 0GKC](https://stacks.math.columbia.edu/tag/0GKC)
* [Stacks Project, Tag 0GJ7](https://stacks.math.columbia.edu/tag/0GJ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.ConstantSheaf

universe u r

attribute [local instance] AlgebraicGeometry.preservesFilteredColimitsOfSize_forget_moduleCatMax

namespace AlgebraicGeometry

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (Λ : Type r) [CommRing Λ]

/-! ### The implication (2) ⟹ (1) of Tag 0GKC -/

/-- Over a Noetherian coefficient ring a finitely generated stalk is the value at a geometric
point of a map of `Λ`-modules from the stalk to the sections over a single étale neighbourhood:
the stalk is then finitely presented, so the identity map factors through a stage of the
filtered colimit of sections defining the stalk. -/
public theorem exists_moduleHom_representing_isFG_etaleStalk [IsNoetherianRing Λ]
    (Q : (SmallEtale B S hS)ᵒᵖ ⥤ ModuleCat.{max (u + 1) r} Λ) (s : GeometricPoint S)
    (hfg : ModuleCat.isFG Λ (etaleStalk B S hS s Q)) :
    ∃ (V : SmallEtale B S hS) (x : (geometricPointFiber B S hS s).obj V)
      (z : etaleStalk B S hS s Q ⟶ Q.obj (op V)),
      ∀ a, (geometricPointSitePoint B S hS s).toPresheafFiber V x Q (z a) = a := by
  set M : ModuleCat.{max (u + 1) r} Λ := etaleStalk B S hS s Q with hM
  rw [ModuleCat.isFG_iff] at hfg
  have : Module.Finite Λ M := hfg
  have : Module.FinitePresentation Λ M := Module.finitePresentation_of_finite Λ M
  obtain ⟨e, ψ, hψ⟩ := Module.FinitePresentation.exists_comp_eq_of_isColimit
    ((geometricPointSitePoint B S hS s).isColimitPresheafFiberCocone Q) (𝟙 M)
  refine ⟨e.unop.1, e.unop.2, ψ, fun a => ?_⟩
  have h := ConcreteCategory.congr_hom hψ a
  rw [CategoryTheory.comp_apply] at h
  exact h.trans (CategoryTheory.id_apply a)

/-- **Stacks Project, Tag 0GKC, the implication (2) ⟹ (1).** On a scheme every quasi-compact
open of which has finitely many irreducible components, a sheaf of modules over a Noetherian
ring on the small étale site whose stalks are finitely generated and whose specialization maps
are bijective is finite type locally constant. -/
@[sga "4 IX 2.13" "(i), special case"]
public theorem isFiniteTypeLocallyConstantModuleSheaf_of_isFG_etaleStalk [IsNoetherianRing Λ]
    (hScomp : ∀ V : S.Opens, IsCompact (V : Set S) → (irreducibleComponents V).Finite)
    (F : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{max (u + 1) r} Λ))
    (hfg : ∀ s : GeometricPoint S, ModuleCat.isFG Λ (etaleStalk B S hS s F.obj))
    (hsp : ∀ (s : GeometricPoint S) (σ : GeometricSpecialization B S hS s),
      Function.Bijective (specializationMapOnStalks σ F.obj)) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r} (SmallEtale.topology B S hS) Λ F := by
  classical
  intro W
  have key : ∀ i : Σ s : GeometricPoint S, (geometricPointFiber B S hS s).obj W,
      ∃ (V : SmallEtale B S hS) (f : V ⟶ W) (y : (geometricPointFiber B S hS i.1).obj V),
        (geometricPointFiber B S hS i.1).map f y = i.2 ∧
          ∃ M : ModuleCat.{max (u + 1) r} Λ, ModuleCat.isFG Λ M ∧ Nonempty
            ((constantSheaf ((SmallEtale.topology B S hS).over V)
                (ModuleCat.{max (u + 1) r} Λ)).obj M ≅
              ((SmallEtale.topology B S hS).overPullback
                (ModuleCat.{max (u + 1) r} Λ) V).obj F) := by
    rintro ⟨s, x⟩
    obtain ⟨W₀, x₀, z₀, hz₀⟩ :=
      exists_moduleHom_representing_isFG_etaleStalk B S hS Λ F.obj s (hfg s)
    obtain ⟨Z, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs
      (Functor.elementsMk (geometricPointFiber B S hS s) W x)
      (Functor.elementsMk (geometricPointFiber B S hS s) W₀ x₀)
    set z : etaleStalk B S hS s F.obj ⟶ F.obj.obj (op Z.1) := z₀ ≫ F.obj.map b.1.op with hzdef
    have hzapp : ∀ α, z α = F.obj.map b.1.op (z₀ α) := fun α =>
      CategoryTheory.comp_apply z₀ (F.obj.map b.1.op) α
    have hgermZ : ∀ α, (geometricPointSitePoint B S hS s).toPresheafFiber Z.1 Z.2 F.obj (z α) =
        α := by
      intro α
      rw [hzapp]
      refine Eq.trans
        ((geometricPointSitePoint B S hS s).toPresheafFiber_w_apply b.1 Z.2 F.obj (z₀ α)) ?_
      exact Eq.trans (congrArg (fun y : (geometricPointFiber B S hS s).obj W₀ =>
          (geometricPointSitePoint B S hS s).toPresheafFiber W₀ y F.obj (z₀ α))
        (b.2 : (geometricPointFiber B S hS s).map b.1 Z.2 = x₀)) (hz₀ α)
    have hetale : Etale (B.inclusion.map Z.1.obj.hom) := Z.1.property
    obtain ⟨O, hO⟩ := exists_opens_of_geometricPoint_specialization_invariant
      (finiteIrreducibleComponents_of_etale (B.inclusion.map Z.1.obj.hom) hScomp)
      (fun r : GeometricPoint Z.1.obj.left.1 => Function.Bijective fun α =>
        (geometricPointSitePoint B S hS (r.map (B.inclusion.map Z.1.obj.hom))).toPresheafFiber
          Z.1 ⟨r.hom, rfl⟩ F.obj (z α))
      (fun r t hrt => bijective_concreteGerm_iff_of_specializes B S hS Z.1 F.obj hsp
        (fun α => z α) r t hrt)
    have hwO : Z.2.1 default ∈ O := by
      refine (hO ⟨s.residueField, Z.2.1⟩).mpr ?_
      refine (bijective_concreteGerm_lift_iff B S hS Z.1 F.obj (fun α => z α) s Z.2).mpr ?_
      have hid : (fun α => (geometricPointSitePoint B S hS s).toPresheafFiber Z.1 Z.2 F.obj
          (z α)) = id := funext hgermZ
      rw [hid]
      exact Function.bijective_id
    have hrange : Set.range Z.2.1.base ⊆ Set.range O.ι.base := by
      rintro _ ⟨d, rfl⟩
      rw [Scheme.Opens.range_ι, Subsingleton.elim d default]
      exact hwO
    have hp : IsOpenImmersion.lift O.ι Z.2.1 hrange ≫ O.ι = Z.2.1 :=
      IsOpenImmersion.lift_fac O.ι Z.2.1 hrange
    have hsize : B.Contains O.toScheme :=
      Scheme.size_lt_of_isOpenImmersion O.ι Z.1.obj.left.property
    let V : SmallEtale B S hS :=
      ⟨Over.mk (Y := B.obj O.toScheme hsize)
        (ObjectProperty.homMk (O.ι ≫ B.inclusion.map Z.1.obj.hom)), by
        change Etale (O.ι ≫ B.inclusion.map Z.1.obj.hom)
        infer_instance⟩
    let ιO : V ⟶ Z.1 := ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk O.ι) rfl)
    have hl : IsOpenImmersion.lift O.ι Z.2.1 hrange ≫ O.ι ≫ B.inclusion.map Z.1.obj.hom =
        s.hom := by
      rw [← Category.assoc, hp]
      exact Z.2.2
    refine ⟨V, ιO ≫ a.1, ⟨IsOpenImmersion.lift O.ι Z.2.1 hrange, hl⟩, ?_,
      etaleStalk B S hS s F.obj, hfg s, ?_⟩
    · have hy : (geometricPointFiber B S hS s).map ιO
          ⟨IsOpenImmersion.lift O.ι Z.2.1 hrange, hl⟩ = Z.2 := Subtype.ext hp
      rw [Functor.map_comp, ConcreteCategory.comp_apply, hy]
      exact a.2
    · refine isConstant_overPullback_of_bijective_germHom B S hS F V
        (E := etaleStalk B S hS s F.obj) (z ≫ F.obj.map ιO.op) ?_
      intro r w
      have hw : ((geometricPointFiber B S hS r).map ιO w).1 default ∈ O := by
        change (w.1 ≫ O.ι) default ∈ O
        rw [Scheme.Hom.comp_apply]
        exact (w.1 default).property
      have h1 := (hO ⟨r.residueField, ((geometricPointFiber B S hS r).map ιO w).1⟩).mp hw
      have h2 := (bijective_concreteGerm_lift_iff B S hS Z.1 F.obj (fun α => z α) r
        ((geometricPointFiber B S hS r).map ιO w)).mp h1
      have h3 : ∀ α, (geometricPointSitePoint B S hS r).toPresheafFiber V w F.obj
          ((z ≫ F.obj.map ιO.op) α) =
          (geometricPointSitePoint B S hS r).toPresheafFiber Z.1
            ((geometricPointFiber B S hS r).map ιO w) F.obj (z α) := fun α => by
        rw [CategoryTheory.comp_apply]
        exact (geometricPointSitePoint B S hS r).toPresheafFiber_w_apply ιO w F.obj (z α)
      exact Eq.mpr (congrArg Function.Bijective (funext h3)) h2
  choose V f y hy M hMfg hMiso using key
  refine ⟨Σ s : GeometricPoint S, (geometricPointFiber B S hS s).obj W, V, f, ?_,
    fun i => ⟨M i, hMfg i, hMiso i⟩⟩
  refine SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective B S hS V f fun pt => ?_
  refine ⟨⟨(GeometricPoint.ofPoint W.obj.left.1 pt).map (B.inclusion.map W.obj.hom),
    ⟨(GeometricPoint.ofPoint W.obj.left.1 pt).hom, rfl⟩⟩, (y _).1 default, ?_⟩
  have h := congrArg (fun q : (geometricPointFiber B S hS
      ((GeometricPoint.ofPoint W.obj.left.1 pt).map (B.inclusion.map W.obj.hom))).obj W =>
    q.1 default) (hy ⟨(GeometricPoint.ofPoint W.obj.left.1 pt).map (B.inclusion.map W.obj.hom),
      ⟨(GeometricPoint.ofPoint W.obj.left.1 pt).hom, rfl⟩⟩)
  refine h.trans ?_
  exact GeometricPoint.ofPoint_liesOver W.obj.left.1 pt

/-! ### The equivalence of Tag 0GKC -/

/-- **Stacks Project, Tag 0GKC.** Let `S` be a scheme such that every quasi-compact open of `S`
has a finite number of irreducible components, let `Λ` be a Noetherian ring and let `F` be a
sheaf of `Λ`-modules on the small étale site of `S`. Then `F` is a finite type locally constant
sheaf of `Λ`-modules if and only if all its stalks at geometric points are finite, i.e.
finitely generated, `Λ`-modules and all specialization maps between stalks are bijective. -/
@[stacks 0GKC, sga "4 IX 2.13" "(i), special case"]
public theorem isFiniteTypeLocallyConstantModuleSheaf_iff_isFG_etaleStalk_and_bijective
    [IsNoetherianRing Λ]
    (hqc : ∀ V : S.Opens, IsCompact (V : Set S) → (irreducibleComponents V).Finite)
    (F : Sheaf (SmallEtale.topology B S hS) (ModuleCat.{max (u + 1) r} Λ)) :
    IsFiniteTypeLocallyConstantModuleSheaf.{u, u + 1, r} (SmallEtale.topology B S hS) Λ F ↔
      (∀ s : GeometricPoint S, ModuleCat.isFG Λ (etaleStalk B S hS s F.obj)) ∧
        ∀ (s : GeometricPoint S) (σ : GeometricSpecialization B S hS s),
          Function.Bijective (specializationMapOnStalks σ F.obj) :=
  ⟨fun hF ↦ ⟨fun s ↦ isFG_etaleStalk_of_isFiniteTypeLocallyConstantModuleSheaf B S hS Λ F hF s,
      fun s σ ↦ bijective_specializationMapOnStalks_of_isFiniteTypeLocallyConstantModuleSheaf
        B S hS Λ F hF s σ⟩,
    fun h ↦ isFiniteTypeLocallyConstantModuleSheaf_of_isFG_etaleStalk B S hS Λ hqc F h.1 h.2⟩

end AlgebraicGeometry

end
