module

public import StacksFrontier.AlgebraicGeometry.Spaces.FiniteTypeFilteredColimit
public import StacksFrontier.AlgebraicGeometry.Spaces.Limits.AffineSectionsOfColimitInjective
public import StacksFrontier.AlgebraicGeometry.Spaces.SmallEtaleModelCoveringSet

/-!
# A finite type module killed in a filtered colimit is killed at a stage

Let `X` be a quasi-compact algebraic space, `D` a filtered diagram of `𝒪_X`-modules with colimit
`c`, and `g : 𝒢 ⟶ D_k` a map out of an `𝒪_X`-module of finite type whose composite with the
colimit map `D_k ⟶ colim D` is zero.  Then `g` already dies at a later stage: `g ≫ D(k ⟶ l) = 0`
for some `k ⟶ l`. In particular, if the transition maps are epimorphisms, some `D_k` is of finite
type and the colimit is zero, then some `D_l` is zero.

## Main results

* `AlgebraicGeometry.Space.exists_comp_map_eq_zero_of_isColimit_of_isFiniteType`: a map out of
  a module of finite type which dies in a filtered colimit dies at a stage.
* `AlgebraicGeometry.Space.exists_isZero_of_isColimit_of_epi_of_isZero`: a filtered colimit
  with epimorphic transition maps of modules one of which is of finite type is zero only if one
  of its stages is.

## References

* [Stacks Project, Tag 0GV1](https://stacks.math.columbia.edu/tag/0GV1)
* [Stacks Project, Tag 03H6](https://stacks.math.columbia.edu/tag/03H6)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits Opposite Stacks.SheafOfModules

universe u

namespace AlgebraicGeometry.Space

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}
  {F : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} {hF : IsAlgebraicSpace B S hS F}

/-- Finitely many sections over affine charts which die in a filtered colimit die at one common
stage. -/
private theorem exists_map_eq_zero_of_isColimit_of_finite {K : Type u} [SmallCategory K]
    [IsFiltered K] {D : K ⥤ Modules.{u, u} B S hS F hF} {c : Cocone D} (hc : IsColimit c)
    {T : Type*} [Finite T] {U : T → SmallEtale B S hS F}
    (hU : ∀ t, IsAffine ((BigFppfOver.toScheme B S hS).obj ((SmallEtale.toOver B S hS F).obj
      (U t))))
    (k : K) (y : ∀ t, (D.obj k).val.obj (op (U t)))
    (hy : ∀ t, (c.ι.app k).val.app (op (U t)) (y t) = 0) :
    ∃ (l : K) (f : k ⟶ l), ∀ t, (D.map f).val.app (op (U t)) (y t) = 0 := by
  classical
  cases nonempty_fintype T
  suffices h : ∀ s : Finset T, ∃ (l : K) (f : k ⟶ l),
      ∀ t ∈ s, (D.map f).val.app (op (U t)) (y t) = 0 by
    obtain ⟨l, f, hf⟩ := h Finset.univ
    exact ⟨l, f, fun t => hf t (Finset.mem_univ t)⟩
  intro s
  induction s using Finset.induction_on with
  | empty => exact ⟨k, 𝟙 k, fun t ht => absurd ht (Finset.notMem_empty t)⟩
  | insert a s ha ih =>
    obtain ⟨l, f, hf⟩ := ih
    have hya : (c.ι.app l).val.app (op (U a)) ((D.map f).val.app (op (U a)) (y a)) = 0 :=
      (congrArg (fun φ : D.obj k ⟶ c.pt => φ.val.app (op (U a)) (y a)) (c.w f)).trans (hy a)
    obtain ⟨m, g, hg⟩ := exists_map_eq_zero_of_isColimit hc (hU a) l _ hya
    have hcomp : ∀ t, (D.map (f ≫ g)).val.app (op (U t)) (y t) =
        (D.map g).val.app (op (U t)) ((D.map f).val.app (op (U t)) (y t)) := fun t => by
      rw [D.map_comp, SheafOfModules.comp_val, PresheafOfModules.comp_app,
        ConcreteCategory.comp_apply]
    refine ⟨m, f ≫ g, fun t ht => ?_⟩
    rw [hcomp]
    rcases Finset.mem_insert.1 ht with rfl | ht
    · exact hg
    · rw [hf t ht, map_zero]

/-- **A map out of a module of finite type which dies in a filtered colimit dies at a stage.**
Let `X` be a quasi-compact algebraic space, `D` a filtered diagram of `𝒪_X`-modules with colimit
cocone `c`, and `g : 𝒢 ⟶ D_k` a map from a module of finite type with `g ≫ c_k = 0`.  Then
`g ≫ D(f) = 0` for some `f : k ⟶ l`. -/
theorem exists_comp_map_eq_zero_of_isColimit_of_isFiniteType
    (hqc : IsQuasiCompactSpace B S hS F) {K : Type u} [SmallCategory K] [IsFiltered K]
    {D : K ⥤ Modules.{u, u} B S hS F hF} {c : Cocone D} (hc : IsColimit c)
    {G : Modules.{u, u} B S hS F hF} (hG : G.IsFiniteType) {k : K} (g : G ⟶ D.obj k)
    (hg : g ≫ c.ι.app k = 0) :
    ∃ (l : K) (f : k ⟶ l), g ≫ D.map f = 0 := by
  classical
  have : G.IsFiniteType := hG
  set J := (smallEtaleRingedSite B S hS F hF).J with hJ
  obtain ⟨I₀, W, hW, hgen⟩ := (isFiniteTypeSections_of_isFiniteType (J := J) G).exists_generators
  choose n s hs using hgen
  obtain ⟨A, hAaff, hAcov⟩ := SmallEtale.exists_affineObject_coversTop B S hS F hF hqc
  obtain ⟨ι₁, hι₁, V, f₁, hVaff, hle₁, hcov₁⟩ :=
    SmallEtale.exists_finite_affine_refinement B S hS F A hAaff _ (hW A)
  have := hι₁
  choose b hb using fun t => (Sieve.mem_ofObjects_iff W (f₁ t)).1
    (hle₁ _ (Sieve.ofArrows_mk V f₁ t))
  set q : ∀ t, V t ⟶ W (b t) := fun t => (hb t).some with hq
  have hs₁ : ∀ t, GeneratesLocally J G.val
      (fun j => G.val.restrictₛₗ (q t).op (s (b t) j)) := fun t =>
    generatesLocally_restrict (q t) (hs (b t))
  have hVcov : J.CoversTop V :=
    Stacks.Sites.coversTop_of_exists_hom
      (Stacks.Sites.coversTop_bind hAcov (fun (_ : PUnit.{u + 2}) t => f₁ t) (fun _ => hcov₁))
      fun p => ⟨p.2, ⟨𝟙 _⟩⟩
  have hy : ∀ p : Σ t : ι₁, Fin (n (b t)),
      (c.ι.app k).val.app (op (V p.1))
        (g.val.app (op (V p.1)) (G.val.restrictₛₗ (q p.1).op (s (b p.1) p.2))) = 0 := fun p =>
    (congrArg (fun φ : G ⟶ c.pt => φ.val.app (op (V p.1))
      (G.val.restrictₛₗ (q p.1).op (s (b p.1) p.2))) hg).trans rfl
  obtain ⟨l, f, hf⟩ := exists_map_eq_zero_of_isColimit_of_finite hc
    (T := Σ t : ι₁, Fin (n (b t))) (U := fun p => V p.1) (fun p => hVaff p.1) k _ hy
  refine ⟨l, f, ?_⟩
  set h := g ≫ D.map f with hh
  have hgen0 : ∀ (t : ι₁) (j : Fin (n (b t))),
      h.val.app (op (V t)) (G.val.restrictₛₗ (q t).op (s (b t) j)) = 0 := fun t j =>
    hf ⟨t, j⟩
  have hnat : ∀ {P Q : (SmallEtale B S hS F)ᵒᵖ} (r : P ⟶ Q) (z : G.val.obj P),
      h.val.app Q (G.val.map r z) = (D.obj l).val.map r (h.val.app P z) := fun r z =>
    PresheafOfModules.naturality_apply h.val r z
  have hloc : ∀ (Z : SmallEtale B S hS F) (x : G.val.obj (op Z)), h.val.app (op Z) x = 0 := by
    intro Z x
    refine (Presheaf.IsSheaf.isSeparated (D.obj l).isSheaf) Z _ (hVcov Z)
      (h.val.app (op Z) x) 0 ?_
    intro Y e he
    rw [map_zero]
    obtain ⟨t, ⟨a⟩⟩ := (Sieve.mem_ofObjects_iff V e).1 he
    obtain ⟨R, hR, hlin⟩ := hs₁ t Y a (G.val.map e.op x)
    refine (Presheaf.IsSheaf.isSeparated (D.obj l).isSheaf) Y R hR _ 0 ?_
    intro Y' e' he'
    rw [map_zero]
    obtain ⟨coef, hcoef⟩ := hlin Y' e' he'
    refine (congrArg ((D.obj l).val.map e'.op) (hnat e.op x).symm).trans
      ((hnat e'.op (G.val.map e.op x)).symm.trans ?_)
    refine (congrArg (h.val.app (op Y')) hcoef.symm).trans ?_
    rw [map_sum]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [(h.val.app (op Y')).hom.map_smul]
    refine (congrArg (coef j • ·) ((hnat (e' ≫ a).op
      (G.val.restrictₛₗ (q t).op (s (b t) j))).trans ?_)).trans (smul_zero _)
    rw [hgen0, map_zero]
    rfl
  ext Z x
  exact hloc Z.unop x

/-- **A filtered colimit with epimorphic transition maps of modules on a quasi-compact space is
zero only if one of its stages is**, as soon as one stage is of finite type. -/
theorem exists_isZero_of_isColimit_of_epi_of_isZero
    (hqc : IsQuasiCompactSpace B S hS F) {K : Type u} [SmallCategory K] [IsFiltered K]
    {D : K ⥤ Modules.{u, u} B S hS F hF} {c : Cocone D} (hc : IsColimit c)
    (hepi : ∀ {k l : K} (f : k ⟶ l), Epi (D.map f)) (hzero : IsZero c.pt) {k : K}
    (hk : (D.obj k).IsFiniteType) :
    ∃ l, IsZero (D.obj l) := by
  obtain ⟨l, f, hf⟩ := exists_comp_map_eq_zero_of_isColimit_of_isFiniteType hqc hc hk (𝟙 _)
    (hzero.eq_of_tgt _ _)
  refine ⟨l, (IsZero.iff_id_eq_zero _).2 ?_⟩
  have := hepi f
  rw [Category.id_comp] at hf
  exact (cancel_epi (D.map f)).1 (by rw [hf, Category.comp_id, comp_zero])

end AlgebraicGeometry.Space

end
