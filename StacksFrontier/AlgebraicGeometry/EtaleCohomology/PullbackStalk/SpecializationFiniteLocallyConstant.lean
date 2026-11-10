module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ConstantGerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.ConstantOfBijectiveGerm
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.PullbackStalk.EtaleSpecializationGerm
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.JointlySurjectiveSieves
public import StacksFrontier.CategoryTheory.Sites.LocallyConstant.Defs

/-!
# Finite locally constant sheaves of sets and specialization of stalks

Let `S` be a scheme every quasi-compact open of which has finitely many irreducible components,
and let `F` be a sheaf of sets on the small étale site of `S`. Then `F` is finite locally
constant precisely when all its stalks at geometric points are finite and all specialization
maps between those stalks are bijective.

The forward implication holds without the hypothesis on irreducible components.

## Main results

* `exists_locallyBijective_constantHom_of_isFiniteLocallyConstant`: at every geometric point, a
  finite locally constant sheaf is comparable to a finite constant presheaf over some étale
  neighbourhood of the point.
* `exists_sections_representing_finite_etaleStalk`: a finite stalk is represented by finitely many
  sections over one étale neighbourhood.
* `finite_etaleStalk_and_bijective_specializationMapOnStalks_of_isFiniteLocallyConstant`: a finite
  locally constant sheaf has finite stalks and bijective specialization maps, with no hypothesis
  on irreducible components.
* `isFiniteLocallyConstant_of_finite_etaleStalk_of_bijective_specializationMap`: the converse, when
  every quasi-compact open has finitely many irreducible components.
* `isFiniteLocallyConstant_iff_finite_etaleStalk_and_bijective_specializationMap`: the equivalence
  of the two conditions.

## References

* [Stacks Project, Tag 0GJ7](https://stacks.math.columbia.edu/tag/0GJ7)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite

universe u

namespace AlgebraicGeometry

/-- At every geometric point of `S`, a finite locally constant sheaf of sets on the small étale
site is comparable, over some étale neighbourhood of the point, to a finite constant presheaf by
a locally bijective map. -/
public theorem exists_locallyBijective_constantHom_of_isFiniteLocallyConstant
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))
    [hF : Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B S hS) F]
    (s : GeometricPoint S) :
    ∃ (U : SmallEtale B S hS) (_x : (geometricPointFiber B S hS s).obj U) (E : Type (u + 1)),
      Finite E ∧ ∃ ψ : (Functor.const (Over U)ᵒᵖ).obj E ⟶ (Over.forget U).op ⋙ F.obj,
        Presheaf.IsLocallyInjective ((SmallEtale.topology B S hS).over U) ψ ∧
          Presheaf.IsLocallySurjective ((SmallEtale.topology B S hS).over U) ψ := by
  obtain ⟨I, X, f, hcov, hconst⟩ := hF.exists_finite_cover (SmallEtale.final B S hS)
  obtain ⟨W, g, hg, w, -⟩ := (geometricPointSitePoint B S hS s).jointly_surjective _ hcov
    ((geometricPointSitePoint B S hS s).uniqueFiberObj (SmallEtale.final B S hS)
      (SmallEtale.finalIsTerminal B S hS)).default
  obtain ⟨-, k, -, ⟨i⟩, rfl⟩ := hg
  obtain ⟨E, hE, ⟨ε⟩⟩ := hconst i
  obtain ⟨δ⟩ : Nonempty (sheafify ((SmallEtale.topology B S hS).over (X i))
      ((Functor.const (Over (X i))ᵒᵖ).obj E) ≅ (Over.forget (X i)).op ⋙ F.obj) :=
    ⟨(sheafToPresheaf ((SmallEtale.topology B S hS).over (X i)) (Type (u + 1))).mapIso ε⟩
  exact ⟨X i, (geometricPointFiber B S hS s).map k w, E, hE,
    toSheafify ((SmallEtale.topology B S hS).over (X i))
        ((Functor.const (Over (X i))ᵒᵖ).obj E) ≫ δ.hom,
    inferInstance, inferInstance⟩

/-- A finite locally constant sheaf of sets on the small étale site of a scheme has finite stalks
at all geometric points, and all its specialization maps between stalks are bijective. -/
@[sga "4 IX 2.13" "(i)"]
public theorem finite_etaleStalk_and_bijective_specializationMapOnStalks_of_isFiniteLocallyConstant
    (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))
    [Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B S hS) F] :
    (∀ s : GeometricPoint S, Finite (etaleStalk B S hS s F.obj)) ∧
      ∀ (s : GeometricPoint S) (σ : GeometricSpecialization B S hS s),
        Function.Bijective (specializationMapOnStalks σ F.obj) := by
  refine ⟨fun s ↦ ?_, fun s σ ↦ ?_⟩
  · obtain ⟨U, x, E, hE, ψ, hinj, hsurj⟩ :=
      exists_locallyBijective_constantHom_of_isFiniteLocallyConstant B S hS F s
    exact finite_etaleStalk_of_bijective_constantGerm B S hS s x ψ hinj hsurj
  · obtain ⟨U, x, E, hE, ψ, hinj, hsurj⟩ :=
      exists_locallyBijective_constantHom_of_isFiniteLocallyConstant B S hS F s
    exact bijective_specializationMapOnStalks_of_constantGerm B S hS σ x ψ hinj hsurj

/-! ### The converse -/

variable (B : BigEtaleSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The germ of a restricted section at `w` is the germ of the section at its image `v`. -/
private theorem toPresheafFiber_map_of_hom {C : Type*} [Category C] {J : GrothendieckTopology C}
    (Φ : GrothendieckTopology.Point.{u} J) {P : Cᵒᵖ ⥤ Type (u + 1)} {V W : C} {v : Φ.fiber.obj V}
    {w : Φ.fiber.obj W} (m : W ⟶ V) (hm : Φ.fiber.map m w = v) (c : P.obj (op V)) :
    Φ.toPresheafFiber W w P (P.map m.op c) = Φ.toPresheafFiber V v P c := by
  subst hm
  exact Φ.toPresheafFiber_w_apply m w P c

/-- A finite stalk of a presheaf of sets on the small étale site is represented by a family of
sections over a single étale neighbourhood of the geometric point. -/
public theorem exists_sections_representing_finite_etaleStalk
    (P : (SmallEtale B S hS)ᵒᵖ ⥤ Type (u + 1)) (s : GeometricPoint S)
    [Finite (etaleStalk B S hS s P)] :
    ∃ (U : SmallEtale B S hS) (x : (geometricPointFiber B S hS s).obj U)
      (z : etaleStalk B S hS s P → P.obj (op U)),
      ∀ a, (geometricPointSitePoint B S hS s).toPresheafFiber U x P (z a) = a := by
  classical
  have : Fintype (etaleStalk B S hS s P) := Fintype.ofFinite _
  have hrep : ∀ a : etaleStalk B S hS s P, ∃ (W : SmallEtale B S hS)
      (w : (geometricPointFiber B S hS s).obj W) (c : P.obj (op W)),
      (geometricPointSitePoint B S hS s).toPresheafFiber W w P c = a := by
    intro a
    obtain ⟨W, w, c, hc⟩ :=
      (geometricPointSitePoint B S hS s).toPresheafFiber_jointly_surjective (P := P) a
    exact ⟨W, w, c, hc⟩
  choose V v c hc using hrep
  obtain ⟨W, hW⟩ := IsCofiltered.inf_objs_exists
    (Finset.image (fun a : etaleStalk B S hS s P =>
      Functor.elementsMk (geometricPointFiber B S hS s) (V a) (v a)) Finset.univ)
  have m : ∀ a : etaleStalk B S hS s P,
      W ⟶ Functor.elementsMk (geometricPointFiber B S hS s) (V a) (v a) :=
    fun a => (hW (Finset.mem_image_of_mem _ (Finset.mem_univ a))).some
  refine ⟨W.1, W.2, fun a => P.map (m a).1.op (c a), fun a => ?_⟩
  exact (toPresheafFiber_map_of_hom _ (m a).1 (m a).2 (c a)).trans (hc a)

/-- On a scheme every quasi-compact open of which has finitely many irreducible components, a sheaf
of sets on the small étale site with finite stalks and bijective specialization maps is finite
locally constant. -/
@[sga "4 IX 2.13" "(i), special case"]
public theorem isFiniteLocallyConstant_of_finite_etaleStalk_of_bijective_specializationMap
    (hScomp : ∀ V : S.Opens, IsCompact (V : Set S) → (irreducibleComponents V).Finite)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1)))
    (hfin : ∀ s : GeometricPoint S, Finite (etaleStalk B S hS s F.obj))
    (hsp : ∀ (s : GeometricPoint S) (σ : GeometricSpecialization B S hS s),
      Function.Bijective (specializationMapOnStalks σ F.obj)) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B S hS) F := by
  classical
  refine ⟨fun U => ?_⟩
  have key : ∀ i : Σ s : GeometricPoint S, (geometricPointFiber B S hS s).obj U,
      ∃ (V : SmallEtale B S hS) (f : V ⟶ U) (y : (geometricPointFiber B S hS i.1).obj V),
        (geometricPointFiber B S hS i.1).map f y = i.2 ∧
          ∃ E : Type (u + 1), Finite E ∧ Nonempty
            ((constantSheaf ((SmallEtale.topology B S hS).over V) (Type (u + 1))).obj E ≅
              ((SmallEtale.topology B S hS).overPullback (Type (u + 1)) V).obj F) := by
    rintro ⟨s, x⟩
    have hsfin := hfin s
    obtain ⟨W₀, x₀, z₀, hz₀⟩ := exists_sections_representing_finite_etaleStalk B S hS F.obj s
    obtain ⟨Z, a, b, -⟩ := IsCofilteredOrEmpty.cone_objs
      (Functor.elementsMk (geometricPointFiber B S hS s) U x)
      (Functor.elementsMk (geometricPointFiber B S hS s) W₀ x₀)
    set z : etaleStalk B S hS s F.obj → F.obj.obj (op Z.1) :=
      fun α => F.obj.map b.1.op (z₀ α)
    have hgermZ : ∀ α, (geometricPointSitePoint B S hS s).toPresheafFiber Z.1 Z.2 F.obj (z α) =
        α := by
      intro α
      exact (toPresheafFiber_map_of_hom _ b.1 b.2 (z₀ α)).trans (hz₀ α)
    have hetale : Etale (B.inclusion.map Z.1.obj.hom) := Z.1.property
    obtain ⟨E, hE⟩ := exists_opens_of_geometricPoint_specialization_invariant
      (finiteIrreducibleComponents_of_etale (B.inclusion.map Z.1.obj.hom) hScomp)
      (fun r : GeometricPoint Z.1.obj.left.1 => Function.Bijective fun α =>
        (geometricPointSitePoint B S hS (r.map (B.inclusion.map Z.1.obj.hom))).toPresheafFiber
          Z.1 ⟨r.hom, rfl⟩ F.obj (z α))
      (fun r t hrt => bijective_germ_iff_of_specializes B S hS Z.1 F.obj hsp z r t hrt)
    have hwE : Z.2.1 default ∈ E := by
      refine (hE ⟨s.residueField, Z.2.1⟩).mpr ?_
      refine (bijective_germ_lift_iff B S hS Z.1 F.obj z s Z.2).mpr ?_
      have hid : (fun α => (geometricPointSitePoint B S hS s).toPresheafFiber Z.1 Z.2 F.obj
          (z α)) = id := funext hgermZ
      rw [hid]
      exact Function.bijective_id
    have hrange : Set.range Z.2.1.base ⊆ Set.range E.ι.base := by
      rintro _ ⟨d, rfl⟩
      rw [Scheme.Opens.range_ι, Subsingleton.elim d default]
      exact hwE
    have hp : IsOpenImmersion.lift E.ι Z.2.1 hrange ≫ E.ι = Z.2.1 :=
      IsOpenImmersion.lift_fac E.ι Z.2.1 hrange
    have hsize : B.Contains E.toScheme :=
      Scheme.size_lt_of_isOpenImmersion E.ι Z.1.obj.left.property
    let V : SmallEtale B S hS :=
      ⟨Over.mk (Y := B.obj E.toScheme hsize)
        (ObjectProperty.homMk (E.ι ≫ B.inclusion.map Z.1.obj.hom)), by
        change Etale (E.ι ≫ B.inclusion.map Z.1.obj.hom)
        infer_instance⟩
    let ιE : V ⟶ Z.1 := ObjectProperty.homMk (Over.homMk (ObjectProperty.homMk E.ι) rfl)
    refine ⟨V, ιE ≫ a.1, ⟨IsOpenImmersion.lift E.ι Z.2.1 hrange, ?_⟩, ?_,
      etaleStalk B S hS s F.obj, hsfin, ?_⟩
    · change IsOpenImmersion.lift E.ι Z.2.1 hrange ≫ E.ι ≫ B.inclusion.map Z.1.obj.hom = s.hom
      rw [← Category.assoc, hp]
      exact Z.2.2
    · have hy : (geometricPointFiber B S hS s).map ιE
          ⟨IsOpenImmersion.lift E.ι Z.2.1 hrange, by
            change IsOpenImmersion.lift E.ι Z.2.1 hrange ≫ E.ι ≫
              B.inclusion.map Z.1.obj.hom = s.hom
            rw [← Category.assoc, hp]
            exact Z.2.2⟩ = Z.2 := Subtype.ext hp
      rw [Functor.map_comp, ConcreteCategory.comp_apply, hy]
      exact a.2
    · refine isConstant_overPullback_of_bijective_germ B S hS F V
        (fun α => F.obj.map ιE.op (z α)) ?_
      intro r w
      have hw : ((geometricPointFiber B S hS r).map ιE w).1 default ∈ E := by
        change (w.1 ≫ E.ι) default ∈ E
        rw [Scheme.Hom.comp_apply]
        exact (w.1 default).property
      have h1 := (hE ⟨r.residueField, ((geometricPointFiber B S hS r).map ιE w).1⟩).mp hw
      have h2 := (bijective_germ_lift_iff B S hS Z.1 F.obj z r
        ((geometricPointFiber B S hS r).map ιE w)).mp h1
      have h3 : ∀ α, (geometricPointSitePoint B S hS r).toPresheafFiber V w F.obj
          (F.obj.map ιE.op (z α)) =
          (geometricPointSitePoint B S hS r).toPresheafFiber Z.1
            ((geometricPointFiber B S hS r).map ιE w) F.obj (z α) :=
        fun α => toPresheafFiber_map_of_hom _ ιE rfl (z α)
      exact Eq.mpr (congrArg Function.Bijective (funext h3)) h2
  choose V f y hy E hEfin hEiso using key
  refine ⟨Σ s : GeometricPoint S, (geometricPointFiber B S hS s).obj U, V, f, ?_,
    fun i => ⟨E i, hEfin i, hEiso i⟩⟩
  refine SmallEtale.generate_ofArrows_mem_topology_of_jointlySurjective B S hS V f fun pt => ?_
  refine ⟨⟨(GeometricPoint.ofPoint U.obj.left.1 pt).map (B.inclusion.map U.obj.hom),
    ⟨(GeometricPoint.ofPoint U.obj.left.1 pt).hom, rfl⟩⟩, (y _).1 default, ?_⟩
  have h := congrArg (fun q : (geometricPointFiber B S hS
      ((GeometricPoint.ofPoint U.obj.left.1 pt).map (B.inclusion.map U.obj.hom))).obj U =>
    q.1 default) (hy ⟨(GeometricPoint.ofPoint U.obj.left.1 pt).map (B.inclusion.map U.obj.hom),
      ⟨(GeometricPoint.ofPoint U.obj.left.1 pt).hom, rfl⟩⟩)
  exact h.trans (GeometricPoint.ofPoint_liesOver U.obj.left.1 pt)

/-- Let `S` be a scheme every quasi-compact open of which has finitely many irreducible components
and let `F` be a sheaf of sets on the small étale site of `S`. Then `F` is finite locally constant
if and only if all its stalks at geometric points are finite and all specialization maps between
those stalks are bijective. -/
@[stacks 0GJ7, sga "4 IX 2.13" "(i), special case"]
public theorem isFiniteLocallyConstant_iff_finite_etaleStalk_and_bijective_specializationMap
    (hScomp : ∀ V : S.Opens, IsCompact (V : Set S) → (irreducibleComponents V).Finite)
    (F : Sheaf (SmallEtale.topology B S hS) (Type (u + 1))) :
    Stacks.ConstantSheaf.IsFiniteLocallyConstant (SmallEtale.topology B S hS) F ↔
      (∀ s : GeometricPoint S, Finite (etaleStalk B S hS s F.obj)) ∧
        ∀ (s : GeometricPoint S) (σ : GeometricSpecialization B S hS s),
          Function.Bijective (specializationMapOnStalks σ F.obj) :=
  ⟨fun _ =>
      finite_etaleStalk_and_bijective_specializationMapOnStalks_of_isFiniteLocallyConstant
        B S hS F,
    fun h => isFiniteLocallyConstant_of_finite_etaleStalk_of_bijective_specializationMap
      B S hS hScomp F h.1 h.2⟩

end AlgebraicGeometry

end
