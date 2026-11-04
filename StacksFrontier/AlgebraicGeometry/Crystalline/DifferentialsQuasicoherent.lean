module

public import Mathlib.Algebra.Category.ModuleCat.Sheaf.Free
public import StacksFrontier.AlgebraicGeometry.AffineDifferentials.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohEquivalence.Basic
public import StacksFrontier.AlgebraicGeometry.AffineQcohPushforward.Colimits
public import StacksFrontier.AlgebraicGeometry.Crystalline.RelativeDifferentialsQuotient
public import StacksFrontier.AlgebraicGeometry.Modules.QuasicoherentBaseChange
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.FormallySmooth.Differentials

/-!
# The divided power differentials as the quotient of the relative differentials by the relations

Let `(T, J, δ)` be a divided power scheme and `f : T → Y` a morphism of schemes.  Inside the sheaf
of relative differentials `Ω_{T/Y}` sits the subsheaf `R` of sections which are, locally on the
open where they live, combinations of the divided power relations
`d (δ_{n+1} x) - δ_n x · d x` of the local sections `x` of `J`.  The comparison map
`Ω_{T/Y} → Ω_{T/Y,δ}` kills `R`, and the quotient `Ω_{T/Y} / R` carries a divided power
derivation, so the two universal properties identify `Ω_{T/Y,δ}` with that quotient.  No
injectivity statement is needed: both composites are identities by the uniqueness halves of the
two universal properties.

## Main definitions

* `Crystalline.dpRelationSpan` — the submodule of the sections of `Ω_{T/Y}` over an open spanned
  by the divided power relations there.
* `Crystalline.dpRelationSubmodule` — the subsheaf `R`, defined as the local saturation of that
  span, so that its sections are by construction locally combinations of relations.
* `Crystalline.dpQuotient` — the quotient `Ω_{T/Y} / R`, and `Crystalline.dpQuotientDerivation`
  its divided power derivation.
* `Crystalline.dpPresentation` — over an affine open `V` of `T`, the map to `Ω_{T/Y}|_V` from the
  free module on the divided power relations of the sections of `J` over `V`.

## Main results

* `Crystalline.dpRelationSpan_map` — restriction carries the span of the relations into the span
  of the relations.
* `Crystalline.toDpDifferentials_apply_eq_zero` — the comparison map kills every section of `R`.
* `Crystalline.dpDifferentialsIsoQuotient` — `Ω_{T/Y,δ} ≅ Ω_{T/Y} / R`.
* `Crystalline.dpPresentation_relation_vanish` — over an affine open the subsheaf `R` dies in the
  cokernel of that presentation, because the divided power ideal is quasi-coherent and so over a
  basic open every relation is a combination of the restrictions of the relations over `V`.
* `Crystalline.dpDifferentialsSheaf_isQuasicoherent` — `Ω_{T/Y,δ}` is quasi-coherent.

## References

* [Stacks Project, Tag 07IY](https://stacks.math.columbia.edu/tag/07IY)
-/

@[expose] public noncomputable section

open CategoryTheory AlgebraicGeometry CategoryTheory.Limits Opposite TopologicalSpace
open scoped AlgebraicGeometry

universe u

namespace Crystalline

variable (T : DividedPowerScheme.{u}) (Y : Scheme.{u}) (f : T.scheme ⟶ Y)

/-! ### The span of the divided power relations -/

/-- The divided power relations over an open, as a set of sections of `Ω_{T/Y}` there. -/
def dpRelationSet (W : T.scheme.Opens) :
    Set ↥((Scheme.Hom.relativeDifferentials f).val.obj (op W)) :=
  Set.range fun z : ↥(sectionIdeal T.scheme.sheaf T.ideal (op W)) × ℕ ↦
    dpRelationSection T Y f W z.1 z.2

/-- The submodule of the sections of `Ω_{T/Y}` over an open spanned by the divided power
relations of the sections of the divided power ideal there. -/
def dpRelationSpan (W : T.scheme.Opens) :
    Submodule ↑(T.scheme.ringCatSheaf.obj.obj (op W))
      ↥((Scheme.Hom.relativeDifferentials f).val.obj (op W)) :=
  Submodule.span _ (dpRelationSet T Y f W)

/-- Each divided power relation lies in the span of the divided power relations. -/
theorem dpRelationSection_mem_span (W : T.scheme.Opens)
    (x : ↥(sectionIdeal T.scheme.sheaf T.ideal (op W))) (n : ℕ) :
    dpRelationSection T Y f W x n ∈ dpRelationSpan T Y f W :=
  Submodule.subset_span ⟨(x, n), rfl⟩

/-- **Restriction carries the span of the divided power relations into the span of the divided
power relations**, because it carries each relation to a relation. -/
theorem dpRelationSpan_map {W W' : T.scheme.Opens} (i : op W ⟶ op W')
    {s : ↥((Scheme.Hom.relativeDifferentials f).val.obj (op W))}
    (hs : s ∈ dpRelationSpan T Y f W) :
    (Scheme.Hom.relativeDifferentials f).val.map i s ∈ dpRelationSpan T Y f W' := by
  have hle : dpRelationSpan T Y f W ≤
      (dpRelationSpan T Y f W').comap
        ((Scheme.Hom.relativeDifferentials f).val.restrictₛₗ i) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨x, n⟩, rfl⟩
    have h : (Scheme.Hom.relativeDifferentials f).val.map i (dpRelationSection T Y f W x n) ∈
        dpRelationSpan T Y f W' := by
      rw [map_dpRelationSection]
      exact dpRelationSection_mem_span T Y f W' _ n
    exact h
  exact hle hs

/-- Two successive restrictions of a section of `Ω_{T/Y}` are one restriction. -/
private theorem relDiff_map_map {W V V' : T.scheme.Opens} (h₁ : V ≤ W) (h₂ : V' ≤ V)
    (s : ↥((Scheme.Hom.relativeDifferentials f).val.obj (op W))) :
    (Scheme.Hom.relativeDifferentials f).val.map (homOfLE h₂).op
        ((Scheme.Hom.relativeDifferentials f).val.map (homOfLE h₁).op s) =
      (Scheme.Hom.relativeDifferentials f).val.map (homOfLE (h₂.trans h₁)).op s :=
  ((Scheme.Hom.relativeDifferentials f).val.map_comp_apply (homOfLE h₁).op (homOfLE h₂).op s).symm

/-- A restricted section lying in the span of the relations restricts into the smaller span. -/
private theorem dpRelationSpan_map_map {W V V' : T.scheme.Opens} (h₁ : V ≤ W) (h₂ : V' ≤ V)
    {s : ↥((Scheme.Hom.relativeDifferentials f).val.obj (op W))}
    (hs : (Scheme.Hom.relativeDifferentials f).val.map (homOfLE h₁).op s ∈
      dpRelationSpan T Y f V) :
    (Scheme.Hom.relativeDifferentials f).val.map (homOfLE (h₂.trans h₁)).op s ∈
      dpRelationSpan T Y f V' := by
  have h := dpRelationSpan_map T Y f (homOfLE h₂).op hs
  rwa [relDiff_map_map] at h

/-! ### The subsheaf of divided power relations -/

/-- **The subsheaf of divided power relations** inside `Ω_{T/Y}`: a section over `W` belongs to it
when every point of `W` has a neighbourhood in `W` over which the section is a combination of
divided power relations. -/
def dpRelationSubmodule : (Scheme.Hom.relativeDifferentials f).Submodule where
  toSubmodule :=
    { obj := fun W ↦
        { carrier := {s | ∀ p ∈ W.unop, ∃ (V : T.scheme.Opens) (h : V ≤ W.unop), p ∈ V ∧
            (Scheme.Hom.relativeDifferentials f).val.map (homOfLE h).op s ∈
              dpRelationSpan T Y f V}
          add_mem' := by
            rintro s t hs ht p hp
            obtain ⟨Vs, hsle, hps, hsmem⟩ := hs p hp
            obtain ⟨Vt, htle, hpt, htmem⟩ := ht p hp
            refine ⟨Vs ⊓ Vt, inf_le_left.trans hsle, ⟨hps, hpt⟩, ?_⟩
            have hs' := dpRelationSpan_map T Y f (homOfLE (inf_le_left (a := Vs) (b := Vt))).op
              hsmem
            have ht' := dpRelationSpan_map T Y f (homOfLE (inf_le_right (a := Vs) (b := Vt))).op
              htmem
            rw [relDiff_map_map] at hs' ht'
            rw [map_add]
            exact Submodule.add_mem _ hs' ht'
          zero_mem' := by
            intro p hp
            refine ⟨W.unop, le_rfl, hp, ?_⟩
            rw [map_zero]
            exact Submodule.zero_mem _
          smul_mem' := by
            rintro c s hs p hp
            obtain ⟨V, hle, hpV, hmem⟩ := hs p hp
            refine ⟨V, hle, hpV, ?_⟩
            rw [PresheafOfModules.map_smul]
            exact Submodule.smul_mem _ _ hmem }
      map := by
        rintro W W' i s hs p hp
        obtain ⟨V, hle, hpV, hmem⟩ := hs p (i.unop.le hp)
        refine ⟨V ⊓ W'.unop, inf_le_right, ⟨hpV, hp⟩, ?_⟩
        have h := dpRelationSpan_map T Y f
          (homOfLE (inf_le_left (a := V) (b := W'.unop))).op hmem
        rw [relDiff_map_map] at h
        have hi : (Scheme.Hom.relativeDifferentials f).val.map
            (homOfLE (inf_le_right (a := V) (b := W'.unop))).op
              ((Scheme.Hom.relativeDifferentials f).val.restrictₛₗ i s) =
            (Scheme.Hom.relativeDifferentials f).val.map
              (homOfLE (inf_le_left.trans hle : V ⊓ W'.unop ≤ W.unop)).op s := by
          rw [PresheafOfModules.restrictₛₗ_apply,
            ← (Scheme.Hom.relativeDifferentials f).val.map_comp_apply]
          exact (Scheme.Hom.relativeDifferentials f).val.congr_map_apply (Subsingleton.elim _ _) s
        rwa [hi] }
  isSheaf := by
    rintro W s hs p hp
    obtain ⟨V, g, hg, hpV⟩ := hs p hp
    obtain ⟨V', h', hpV', hmem⟩ := hg p hpV
    refine ⟨V', h'.trans g.le, hpV', ?_⟩
    have hcomp : (Scheme.Hom.relativeDifferentials f).val.map (homOfLE h').op
          ((Scheme.Hom.relativeDifferentials f).val.map g.op s) =
        (Scheme.Hom.relativeDifferentials f).val.map (homOfLE (h'.trans g.le)).op s := by
      rw [← (Scheme.Hom.relativeDifferentials f).val.map_comp_apply]
      exact (Scheme.Hom.relativeDifferentials f).val.congr_map_apply (Subsingleton.elim _ _) s
    rwa [← hcomp]

/-- Each divided power relation is a section of the subsheaf of divided power relations. -/
theorem dpRelationSection_mem_submodule (W : T.scheme.Opens)
    (x : ↥(sectionIdeal T.scheme.sheaf T.ideal (op W))) (n : ℕ) :
    dpRelationSection T Y f W x n ∈ (dpRelationSubmodule T Y f).obj (op W) := by
  intro p hp
  refine ⟨W, le_rfl, hp, ?_⟩
  rw [(Scheme.Hom.relativeDifferentials f).val.congr_map_apply
    (Subsingleton.elim (homOfLE (le_refl W)).op (𝟙 (op W))),
    (Scheme.Hom.relativeDifferentials f).val.map_id]
  exact dpRelationSection_mem_span T Y f W x n

/-! ### The quotient of the relative differentials by the relations -/

/-- The quotient map out of a cokernel is an epimorphism, at the `SheafOfModules` spelling.
Instance search does not match a module spelled `AlgebraicGeometry.Scheme.Modules`, which is a
definition, against the zero morphisms of the category, so the fact is restated and applied
explicitly. -/
theorem epi_cokernelπ {X : Scheme.{u}}
    {M N : _root_.SheafOfModules.{u} X.ringCatSheaf} (g : M ⟶ N) : Epi (cokernel.π g) :=
  inferInstance

/-- The sheaf of divided power differentials, with its type spelled `SheafOfModules` rather than
`AlgebraicGeometry.Scheme.Modules`, which is a definition and so hides the zero morphisms of the
category from instance search. -/
def dpDiffAsSheaf : _root_.SheafOfModules.{u} T.scheme.ringCatSheaf :=
  dpDifferentialsSheaf T Y f

/-- **The quotient of `Ω_{T/Y}` by the subsheaf of divided power relations.** -/
def dpQuotient : T.scheme.Modules := cokernel (dpRelationSubmodule T Y f).ι

/-- The quotient map onto `Ω_{T/Y}` modulo the divided power relations. -/
def dpQuotientMk : Scheme.Hom.relativeDifferentials f ⟶ dpQuotient T Y f :=
  cokernel.π (dpRelationSubmodule T Y f).ι

/-- The sections of the quotient over an open, as a module over the ring of sections of `𝒪_T`
there; the scalars of a presheaf of modules are spelled through the `RingCat`-valued structure
sheaf, so the instance is supplied by name. -/
instance dpQuotientObjModule (W : T.scheme.Opens) :
    Module ↑(T.scheme.sheaf.obj.obj (op W)) ↥((dpQuotient T Y f).val.obj (op W)) :=
  ((dpQuotient T Y f).val.obj (op W)).isModule

/-- The same module structure at the spelling the sections notation uses. -/
instance dpQuotientSectionsModule (W : T.scheme.Opens) :
    Module ↑(T.scheme.sheaf.obj.obj (op W)) Γ(dpQuotient T Y f, W) :=
  ((dpQuotient T Y f).val.obj (op W)).isModule

/-- A scalar of `𝒪_T` acts on the sections of `Ω_{T/Y}` the same way however the ring of
sections is spelled. -/
theorem relDiffSmulCast (W : T.scheme.Opens) (c : ↑(T.scheme.sheaf.obj.obj (op W)))
    (z : ↥((Scheme.Hom.relativeDifferentials f).val.obj (op W))) :
    c • z = (id c : ↑(T.scheme.ringCatSheaf.obj.obj (op W))) • z := rfl

/-- A scalar of `𝒪_T` acts on the sections of the quotient the same way however the ring of
sections is spelled. -/
theorem dpQuotientSmulCast (W : T.scheme.Opens) (c : ↑(T.scheme.sheaf.obj.obj (op W)))
    (z : ↥((dpQuotient T Y f).val.obj (op W))) :
    c • z = (id c : ↑(T.scheme.ringCatSheaf.obj.obj (op W))) • z := rfl

/-- The quotient map kills every section of the subsheaf of divided power relations. -/
theorem dpQuotientMk_apply_eq_zero (W : T.scheme.Opens)
    {s : ↥((Scheme.Hom.relativeDifferentials f).val.obj (op W))}
    (hs : s ∈ (dpRelationSubmodule T Y f).obj (op W)) :
    (dpQuotientMk T Y f).val.app (op W) s = 0 :=
  congrArg
    (fun φ : (dpRelationSubmodule T Y f).toSheafOfModules ⟶ dpQuotient T Y f ↦
      φ.val.app (op W) (⟨s, hs⟩ : ↥((dpRelationSubmodule T Y f).toSheafOfModules.val.obj (op W))))
    (cokernel.condition (dpRelationSubmodule T Y f).ι)

/-- The comparison map kills every section of the span of the divided power relations. -/
theorem toDpDifferentials_apply_span_eq_zero (W : T.scheme.Opens)
    {s : ↥((Scheme.Hom.relativeDifferentials f).val.obj (op W))}
    (hs : s ∈ dpRelationSpan T Y f W) :
    (toDpDifferentials T Y f).val.app (op W) s = 0 := by
  have hle : dpRelationSpan T Y f W ≤
      LinearMap.ker ((toDpDifferentials T Y f).val.app (op W)).hom := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨⟨x, n⟩, rfl⟩
    exact toDpDifferentials_dpRelationSection T Y f W x n
  exact hle hs

/-- A morphism into a sheaf of modules kills a section which it kills locally. -/
private theorem hom_app_eq_zero_of_local {X : Scheme.{u}} {M N : X.Modules} (φ : M ⟶ N)
    {W : X.Opens} {s : ↥(M.val.obj (op W))}
    (h : ∀ p ∈ W, ∃ (V : X.Opens) (hle : V ≤ W), p ∈ V ∧
      φ.val.app (op V) (M.val.map (homOfLE hle).op s) = 0) :
    φ.val.app (op W) s = 0 := by
  refine TopCat.Presheaf.IsSheaf.section_ext N.isSheaf ?_
  intro p hp
  obtain ⟨V, hle, hpV, hV⟩ := h p hp
  refine ⟨V, hle, hpV, ?_⟩
  have hnat := PresheafOfModules.naturality_apply φ.val (homOfLE hle).op s
  rw [hV] at hnat
  exact hnat.symm.trans (map_zero (N.val.map (homOfLE hle).op).hom).symm

/-- **The comparison map kills every section of the subsheaf of divided power relations**: such a
section is locally a combination of relations, and the divided power differentials form a
sheaf. -/
theorem toDpDifferentials_apply_eq_zero (W : T.scheme.Opens)
    {s : ↥((Scheme.Hom.relativeDifferentials f).val.obj (op W))}
    (hs : s ∈ (dpRelationSubmodule T Y f).obj (op W)) :
    (toDpDifferentials T Y f).val.app (op W) s = 0 := by
  refine hom_app_eq_zero_of_local (toDpDifferentials T Y f) fun p hp ↦ ?_
  obtain ⟨V, hle, hpV, hmem⟩ := hs p hp
  exact ⟨V, hle, hpV, toDpDifferentials_apply_span_eq_zero T Y f V hmem⟩

/-- The subsheaf of divided power relations lies in the kernel of the comparison map.  The zero
morphism is ascribed at the `SheafOfModules` spelling, where the category's zero morphisms are
visible to instance search. -/
theorem ι_comp_toDpDifferentials :
    (dpRelationSubmodule T Y f).ι ≫ toDpDifferentials T Y f =
      (0 : (dpRelationSubmodule T Y f).toSheafOfModules ⟶ dpDiffAsSheaf T Y f) := by
  ext W s
  show (toDpDifferentials T Y f).val.app W s.1 = 0
  exact toDpDifferentials_apply_eq_zero T Y f W.unop s.2

/-- **The map from the quotient to the divided power differentials** induced by the comparison
map, which kills the subsheaf of divided power relations. -/
def dpQuotientToDifferentials : dpQuotient T Y f ⟶ dpDifferentialsSheaf T Y f :=
  cokernel.desc (dpRelationSubmodule T Y f).ι (toDpDifferentials T Y f)
    (ι_comp_toDpDifferentials T Y f)

/-- The quotient map followed by `dpQuotientToDifferentials` is the comparison map
`toDpDifferentials`. -/
theorem dpQuotientMk_comp_dpQuotientToDifferentials :
    dpQuotientMk T Y f ≫ dpQuotientToDifferentials T Y f = toDpDifferentials T Y f :=
  cokernel.π_desc (dpRelationSubmodule T Y f).ι (toDpDifferentials T Y f)
    (ι_comp_toDpDifferentials T Y f)

/-! ### The divided power derivation of the quotient -/

/-- The map on sections of the divided power derivation of the quotient: the universal relative
derivation followed by the quotient map. -/
def dpQuotientApp (W : T.scheme.Opens) :
    ↑(T.scheme.sheaf.obj.obj (op W)) → ↥((dpQuotient T Y f).val.obj (op W)) :=
  fun x ↦ (dpQuotientMk T Y f).val.app (op W)
    ((Scheme.Hom.universalRelativeDerivation f).d x)

/-- The divided power derivation of the quotient is additive on sections. -/
theorem dpQuotientApp_add (W : T.scheme.Opens) (x y : ↑(T.scheme.sheaf.obj.obj (op W))) :
    dpQuotientApp T Y f W (x + y) = dpQuotientApp T Y f W x + dpQuotientApp T Y f W y :=
  (congrArg ((dpQuotientMk T Y f).val.app (op W))
      (map_add (Scheme.Hom.universalRelativeDerivation f).d x y)).trans
    (map_add ((dpQuotientMk T Y f).val.app (op W)).hom _ _)

/-- The quotient map is linear over the ring of sections of `𝒪_T`. -/
theorem dpQuotientMk_smul (W : T.scheme.Opens) (c : ↑(T.scheme.sheaf.obj.obj (op W)))
    (z : ↥((Scheme.Hom.relativeDifferentials f).val.obj (op W))) :
    (dpQuotientMk T Y f).val.app (op W) (c • z) =
      c • (dpQuotientMk T Y f).val.app (op W) z := by
  rw [relDiffSmulCast T Y f W, dpQuotientSmulCast T Y f W]
  exact map_smul ((dpQuotientMk T Y f).val.app (op W)).hom _ z

/-- The divided power derivation of the quotient satisfies the Leibniz rule on sections. -/
theorem dpQuotientApp_mul (W : T.scheme.Opens) (x y : ↑(T.scheme.sheaf.obj.obj (op W))) :
    dpQuotientApp T Y f W (x * y) =
      x • dpQuotientApp T Y f W y + y • dpQuotientApp T Y f W x := by
  have hd := (Scheme.Hom.universalRelativeDerivation f).d_mul (X := op W) x y
  show (dpQuotientMk T Y f).val.app (op W)
    ((Scheme.Hom.universalRelativeDerivation f).d (x * y)) = _
  rw [hd, map_add, dpQuotientMk_smul, dpQuotientMk_smul]
  rfl

/-- The divided power derivation of the quotient vanishes on sections pulled back from `Y`. -/
theorem dpQuotientApp_appLE (W : T.scheme.Opens) (V : Y.Opens) (h : W ≤ f ⁻¹ᵁ V)
    (a : Γ(Y, V)) : dpQuotientApp T Y f W ((f.appLE V W h).hom a) = 0 := by
  show (dpQuotientMk T Y f).val.app (op W)
    ((Scheme.Hom.universalRelativeDerivation f).d ((f.appLE V W h).hom a)) = _
  rw [Stacks.AlgebraicGeometry.AffineDifferentials.d_appLE_eq_zero f _
    (Scheme.Hom.universalRelativeDerivation f) V W h a]
  exact map_zero ((dpQuotientMk T Y f).val.app (op W)).hom

/-- The divided power derivation of the quotient obeys the divided power chain rule
$d(\gamma_{n+1}(x)) = \gamma_n(x) \, dx$ on sections of the divided power ideal. -/
theorem dpQuotientApp_dpow (W : T.scheme.Opens) (n : ℕ)
    (x : ↥(sectionIdeal T.scheme.sheaf T.ideal (op W))) :
    dpQuotientApp T Y f W ((T.dividedPowers.dividedPowers (op W)).dpow (n + 1) x) =
      (T.dividedPowers.dividedPowers (op W)).dpow n (x : ↑(T.scheme.sheaf.obj.obj (op W))) •
        dpQuotientApp T Y f W x := by
  have hzero := dpQuotientMk_apply_eq_zero T Y f W
    (dpRelationSection_mem_submodule T Y f W x n)
  rwa [dpRelationSection_eq, dpRelation_eq, map_sub, dpQuotientMk_smul, sub_eq_zero] at hzero

/-- The divided power derivation of the quotient commutes with restriction to a smaller open. -/
theorem dpQuotientApp_naturality {W W' : T.scheme.Opens} (i : W' ⟶ W)
    (x : ↑(T.scheme.sheaf.obj.obj (op W))) :
    (dpQuotient T Y f).val.map i.op (dpQuotientApp T Y f W x) =
      dpQuotientApp T Y f W' (T.scheme.sheaf.obj.map i.op x) := by
  have hd : (Scheme.Hom.universalRelativeDerivation f).d (T.scheme.sheaf.obj.map i.op x) =
      (Scheme.Hom.relativeDifferentials f).val.map i.op
        ((Scheme.Hom.universalRelativeDerivation f).d x) :=
    (Scheme.Hom.universalRelativeDerivation f).d_map i.op x
  show (dpQuotient T Y f).val.map i.op
      ((dpQuotientMk T Y f).val.app (op W)
        ((Scheme.Hom.universalRelativeDerivation f).d x)) = _
  rw [← PresheafOfModules.naturality_apply (dpQuotientMk T Y f).val i.op, ← hd]
  rfl

/-- **The divided power derivation of the quotient**: the universal relative derivation followed
by the quotient map obeys the divided power chain rule, because the relations die in the
quotient. -/
def dpQuotientDerivation : DividedPowerSchemeDerivation T Y f (dpQuotient T Y f) where
  app W := dpQuotientApp T Y f W
  naturality i x := dpQuotientApp_naturality T Y f i x
  dividedPowerDerivation W V h :=
    { toDerivation :=
        Derivation.mk'
          (AddMonoidHom.toIntLinearMap
            (AddMonoidHom.mk' (dpQuotientApp T Y f W) (dpQuotientApp_add T Y f W)))
          (dpQuotientApp_mul T Y f W)
      map_ringHom' a := dpQuotientApp_appLE T Y f W V h a
      map_dpow' n hn x hx := by
        obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := ⟨n - 1, by omega⟩
        exact dpQuotientApp_dpow T Y f W k ⟨x, hx⟩ }
  dividedPowerDerivation_apply _ _ _ _ := rfl

/-! ### The identification -/

/-- **The map from the divided power differentials to the quotient** given by the universal
property of the universal divided power derivation. -/
def differentialsToDpQuotient : dpDifferentialsSheaf T Y f ⟶ dpQuotient T Y f :=
  (universalDPSchemeDerivation_isUniversal T Y f (dpQuotient T Y f)
    (dpQuotientDerivation T Y f)).choose

/-- The map `differentialsToDpQuotient` sends the universal divided power differential of a
section to its image under the divided power derivation of the quotient. -/
theorem differentialsToDpQuotient_app (W : T.scheme.Opens)
    (x : ↑(T.scheme.sheaf.obj.obj (op W))) :
    (differentialsToDpQuotient T Y f).val.app (op W) (sheafApp T Y f W x) =
      dpQuotientApp T Y f W x :=
  (universalDPSchemeDerivation_isUniversal T Y f (dpQuotient T Y f)
    (dpQuotientDerivation T Y f)).choose_spec.1 W x

/-- The map `dpQuotientToDifferentials` sends the image of a section under the divided power
derivation of the quotient to its universal divided power differential. -/
theorem dpQuotientToDifferentials_app (W : T.scheme.Opens)
    (x : ↑(T.scheme.sheaf.obj.obj (op W))) :
    (dpQuotientToDifferentials T Y f).val.app (op W) (dpQuotientApp T Y f W x) =
      sheafApp T Y f W x :=
  (congrArg (fun φ : Scheme.Hom.relativeDifferentials f ⟶ dpDifferentialsSheaf T Y f ↦
      φ.val.app (op W) ((Scheme.Hom.universalRelativeDerivation f).d x))
    (dpQuotientMk_comp_dpQuotientToDifferentials T Y f)).trans
      (toDpDifferentials_d T Y f W x)

/-- **The divided power differentials are the quotient of the relative differentials by the
divided power relations.**  Both composites are identities by the uniqueness halves of the two
universal properties, so no injectivity statement is needed. -/
def dpDifferentialsIsoQuotient : dpDifferentialsSheaf T Y f ≅ dpQuotient T Y f where
  hom := differentialsToDpQuotient T Y f
  inv := dpQuotientToDifferentials T Y f
  hom_inv_id := by
    refine (universalDPSchemeDerivation_isUniversal T Y f).hom_ext
      (E := universalDPSchemeDerivation T Y f) (fun W x ↦ ?_) (fun _ _ ↦ rfl)
    change (dpQuotientToDifferentials T Y f).val.app (op W)
      ((differentialsToDpQuotient T Y f).val.app (op W) (sheafApp T Y f W x)) = _
    rw [differentialsToDpQuotient_app T Y f W x, dpQuotientToDifferentials_app T Y f W x]
    rfl
  inv_hom_id := by
    have key : toDpDifferentials T Y f ≫ differentialsToDpQuotient T Y f =
        dpQuotientMk T Y f := by
      refine (Scheme.Hom.existsUnique_hom_relativeDifferentials f (dpQuotient T Y f)
        ((Scheme.Hom.universalRelativeDerivation f).postcomp
          (dpQuotientMk T Y f).val)).unique ?_ rfl
      ext W a
      have h1 : (toDpDifferentials T Y f).val.app W
          ((Scheme.Hom.universalRelativeDerivation f).d a) = sheafApp T Y f W.unop a :=
        toDpDifferentials_d T Y f W.unop a
      have h2 : (differentialsToDpQuotient T Y f).val.app W (sheafApp T Y f W.unop a) =
          dpQuotientApp T Y f W.unop a := differentialsToDpQuotient_app T Y f W.unop a
      change (differentialsToDpQuotient T Y f).val.app W
          ((toDpDifferentials T Y f).val.app W
            ((Scheme.Hom.universalRelativeDerivation f).d a)) = _
      rw [h1, h2]
      rfl
    have : Epi (cokernel.π (dpRelationSubmodule T Y f).ι) :=
      epi_cokernelπ (dpRelationSubmodule T Y f).ι
    refine (cancel_epi (cokernel.π (dpRelationSubmodule T Y f).ι)).1 ?_
    refine Eq.trans ?_ (Category.comp_id _).symm
    refine (Category.assoc _ _ _).symm.trans ?_
    exact (congrArg (fun φ : Scheme.Hom.relativeDifferentials f ⟶ dpDifferentialsSheaf T Y f ↦
      φ ≫ differentialsToDpQuotient T Y f)
      (dpQuotientMk_comp_dpQuotientToDifferentials T Y f)).trans key

section Affine

/-- Restriction of modules to an open. -/
abbrev dpRestrict (T : DividedPowerScheme.{u}) (V : T.scheme.Opens) :
    T.scheme.Modules ⥤ V.toScheme.Modules :=
  Scheme.Modules.restrictFunctor V.ι

/-- The open of `T` swept out by the whole of `V`. -/
def dpTop (T : DividedPowerScheme.{u}) (V : T.scheme.Opens) : T.scheme.Opens :=
  V.ι ''ᵁ (⊤ : V.toScheme.Opens)

/-- Every open of `V` sweeps out an open inside `dpTop`. -/
theorem image_le_dpTop {T : DividedPowerScheme.{u}} (V : T.scheme.Opens)
    (U : V.toScheme.Opens) : V.ι ''ᵁ U ≤ dpTop T V :=
  Scheme.Hom.image_mono _ le_top

/-- The index type of the relations over `V`. -/
def dpIndex (T : DividedPowerScheme.{u}) (V : T.scheme.Opens) : Type u :=
  ↥(sectionIdeal T.scheme.sheaf T.ideal (op (dpTop T V))) × ℕ

/-- The relation section over an open of `V`, as a section of the relation subsheaf. -/
def dpRelationRestrictedSection (V : T.scheme.Opens) (U : V.toScheme.Opens)
    (i : dpIndex T V) :
    ↥((dpRelationSubmodule T Y f).obj (op (V.ι ''ᵁ U))) :=
  ⟨(Scheme.Hom.relativeDifferentials f).val.map (homOfLE (image_le_dpTop V U)).op
      (dpRelationSection T Y f (dpTop T V) i.1 i.2),
    (dpRelationSubmodule T Y f).map _ (dpRelationSection_mem_submodule T Y f _ i.1 i.2)⟩

/-- The relation sections assemble into a global section of the restricted relation subsheaf. -/
def dpRelationGlobalSection (V : T.scheme.Opens) (i : dpIndex T V) :
    ((dpRestrict T V).obj (dpRelationSubmodule T Y f).toSheafOfModules).sections :=
  PresheafOfModules.sectionsMk (fun U ↦ dpRelationRestrictedSection T Y f V U.unop i)
    (fun {U U'} g ↦ by
      exact Subtype.ext (relDiff_map_map T Y f (image_le_dpTop V U.unop)
        (Scheme.Hom.image_mono _ g.unop.le) _))

/-- The free module on the relation index. -/
abbrev dpFree (T : DividedPowerScheme.{u}) (V : T.scheme.Opens) : V.toScheme.Modules :=
  SheafOfModules.free.{u} (R := V.toScheme.ringCatSheaf) (dpIndex T V)

/-- The map from the free module on the relations to the restricted relation subsheaf. -/
def dpRelationFreeHom (V : T.scheme.Opens) :
    dpFree T V ⟶ (dpRestrict T V).obj (dpRelationSubmodule T Y f).toSheafOfModules :=
  (SheafOfModules.freeHomEquiv _).symm (dpRelationGlobalSection T Y f V)

/-- The presentation map: the free module on the relations, mapped into the restricted
relative differentials. -/
def dpPresentation (V : T.scheme.Opens) :
    dpFree T V ⟶ (dpRestrict T V).obj (Scheme.Hom.relativeDifferentials f) :=
  dpRelationFreeHom T Y f V ≫ (dpRestrict T V).map (dpRelationSubmodule T Y f).ι

/-- Scalars of `𝒪_T` act on the sections of a restricted module through the identification of
the sections over an open of `V` with the sections over its image. -/
theorem restrictSmul (M : T.scheme.Modules) (V : T.scheme.Opens) (U : V.toScheme.Opens)
    (c : ↑Γ(T.scheme, V.ι ''ᵁ U)) (z : ↑Γ(M, V.ι ''ᵁ U)) :
    (id c : ↑Γ(V.toScheme, U)) • (id z : ↑Γ(M.restrict V.ι, U)) = c • z := by
  have h := Scheme.Modules.smul_restrictAppIso_hom_apply V.ι M U (id c) (id z)
  rwa [Scheme.Opens.ι_appIso] at h

/-- The quotient map onto the cokernel of the presentation kills the restricted relations. -/
theorem dpPresentationπ_relation (V : T.scheme.Opens) (U : V.toScheme.Opens)
    (i : dpIndex T V) :
    ((cokernel.π (dpPresentation T Y f V)).val.app (op U)).hom
        (id (dpRelationRestrictedSection T Y f V U i).1) = 0 := by
  have h0 : dpRelationFreeHom T Y f V ≫ ((dpRestrict T V).map (dpRelationSubmodule T Y f).ι ≫
      cokernel.π (dpPresentation T Y f V)) = 0 :=
    (Category.assoc _ _ _).symm.trans (cokernel.condition (dpPresentation T Y f V))
  have h1 : (SheafOfModules.freeHomEquiv (cokernel (dpPresentation T Y f V))).symm
      (fun j ↦ SheafOfModules.sectionsMap
        ((dpRestrict T V).map (dpRelationSubmodule T Y f).ι ≫
          cokernel.π (dpPresentation T Y f V)) (dpRelationGlobalSection T Y f V j)) = 0 :=
    (SheafOfModules.freeHomEquiv_symm_comp (dpRelationGlobalSection T Y f V) _).symm.trans h0
  have h2 := congrFun ((Equiv.symm_apply_eq _).1 h1) i
  exact congrArg (fun z ↦ PresheafOfModules.sections.eval z (op U)) h2

/-- Scalars of `𝒪_T` act on restricted sections however the ring of sections is spelled. -/
theorem smulGammaCast (V : T.scheme.Opens) (U : V.toScheme.Opens)
    (c : ↑Γ(V.toScheme, U))
    (z : ↑Γ((Scheme.Hom.relativeDifferentials f).restrict V.ι, U)) :
    c • z = (id c : ↑(V.toScheme.ringCatSheaf.obj.obj (op U))) •
      (id z : ↥(((dpRestrict T V).obj
        (Scheme.Hom.relativeDifferentials f)).val.obj (op U))) := rfl

/-- Scalars of `𝒪_T` act on the sections of `Ω_{T/Y}` over the image of an open of `V` the same
way as on the sections of the restricted module there. -/
theorem relDiffRestrictSmul (V : T.scheme.Opens) (U : V.toScheme.Opens)
    (c : ↑(T.scheme.sheaf.obj.obj (op (V.ι ''ᵁ U))))
    (z : ↥((Scheme.Hom.relativeDifferentials f).val.obj (op (V.ι ''ᵁ U)))) :
    c • z = (id c : ↑(V.toScheme.ringCatSheaf.obj.obj (op U))) •
      (id z : ↥(((dpRestrict T V).obj
        (Scheme.Hom.relativeDifferentials f)).val.obj (op U))) :=
  (restrictSmul T (Scheme.Hom.relativeDifferentials f) V U (id c) (id z)).symm.trans
    (smulGammaCast T Y f V U (id c) (id z))

/-- The sections of the cokernel of the presentation over an open of `V`, as a module over the
ring of sections of `𝒪_T` on the image open. -/
instance dpPresentationCokernelModule (V : T.scheme.Opens) (U : V.toScheme.Opens) :
    Module ↑(T.scheme.sheaf.obj.obj (op (V.ι ''ᵁ U)))
      ↥((cokernel (dpPresentation T Y f V)).val.obj (op U)) :=
  ((cokernel (dpPresentation T Y f V)).val.obj (op U)).isModule

/-- The quotient map onto the cokernel of the presentation, as a linear map over the ring of
sections of `𝒪_T` on the image of an open of `V`. -/
def dpPresentationπₗ (V : T.scheme.Opens) (U : V.toScheme.Opens) :
    ↥((Scheme.Hom.relativeDifferentials f).val.obj (op (V.ι ''ᵁ U))) →ₗ[↑(T.scheme.sheaf.obj.obj
        (op (V.ι ''ᵁ U)))]
      ↥((cokernel (dpPresentation T Y f V)).val.obj (op U)) where
  toFun z := ((cokernel.π (dpPresentation T Y f V)).val.app (op U)).hom z
  map_add' z w := map_add _ z w
  map_smul' c z := by
    rw [relDiffRestrictSmul T Y f V U c z]
    exact map_smul ((cokernel.π (dpPresentation T Y f V)).val.app (op U)).hom _ _

/-- The sections of `Ω_{T/Y}` over the image of an open of `V` killed by the quotient map onto
the cokernel of the presentation. -/
def dpPresentationKernel (V : T.scheme.Opens) (U : V.toScheme.Opens) :
    Submodule ↑(T.scheme.sheaf.obj.obj (op (V.ι ''ᵁ U)))
      ↥((Scheme.Hom.relativeDifferentials f).val.obj (op (V.ι ''ᵁ U))) :=
  LinearMap.ker (dpPresentationπₗ T Y f V U)

/-- Membership in that kernel is the vanishing of the image section. -/
theorem mem_dpPresentationKernel (V : T.scheme.Opens) (U : V.toScheme.Opens)
    {z : ↥((Scheme.Hom.relativeDifferentials f).val.obj (op (V.ι ''ᵁ U)))} :
    z ∈ dpPresentationKernel T Y f V U ↔
      ((cokernel.π (dpPresentation T Y f V)).val.app (op U)).hom z = 0 := Iff.rfl

/-- Each restricted relation is killed by the quotient map. -/
theorem dpRelationRestricted_mem_kernel (V : T.scheme.Opens) (U : V.toScheme.Opens)
    (i : dpIndex T V) :
    (dpRelationRestrictedSection T Y f V U i).1 ∈ dpPresentationKernel T Y f V U :=
  dpPresentationπ_relation T Y f V U i

/-- The affine open swept out by the whole of `V` is `V`. -/
theorem dpTop_eq (V : T.scheme.Opens) : dpTop T V = V := by
  rw [dpTop, Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]

/-- The quasi-coherent ideal sheaf of `T`, as a module on the underlying scheme. -/
def dpIdealModule (T : DividedPowerScheme.{u}) : T.scheme.Modules := T.ideal.toSheafOfModules

/-- The ideal sheaf of `T`, as a module on the underlying scheme, is quasi-coherent. -/
instance dpIdealModule_isQuasicoherent (T : DividedPowerScheme.{u}) :
    (dpIdealModule T).IsQuasicoherent := T.isQuasicoherent

/-- **Local generation of the divided power ideal.**  Over a basic open of an affine open `V`,
every section of the divided power ideal lies in the submodule generated by the restrictions of
the sections over all of `V`, because the ideal sheaf is quasi-coherent. -/
theorem sectionIdeal_mem_span (V : T.scheme.Opens) (hV : IsAffineOpen (dpTop T V))
    (a : ↑Γ(T.scheme, dpTop T V)) {W : T.scheme.Opens} (hW : W = T.scheme.basicOpen a)
    (hWV : W ≤ dpTop T V) (y : ↥(sectionIdeal T.scheme.sheaf T.ideal (op W))) :
    (y : ↑(T.scheme.sheaf.obj.obj (op W))) ∈
      Submodule.span ↑(T.scheme.sheaf.obj.obj (op W))
        (Set.range fun x : ↥(sectionIdeal T.scheme.sheaf T.ideal (op (dpTop T V))) ↦
          (DividedPowerStructure.restrict T.ideal (homOfLE hWV).op x :
            ↑(T.scheme.sheaf.obj.obj (op W)))) := by
  let := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.moduleOfLE (dpIdealModule T) hWV
  have hloc := Stacks.AlgebraicGeometry.QuasicoherentBaseChange.isLocalizedModule_restrictₗ
    (dpIdealModule T) hV a hW hWV
  obtain ⟨n, x, hx⟩ := IsLocalizedModule.Away.surj
    (Stacks.AlgebraicGeometry.QuasicoherentBaseChange.restrictₗ (dpIdealModule T) hWV) a y
  subst hW
  obtain ⟨u, hu⟩ : IsUnit (id (T.scheme.presheaf.map (homOfLE hWV).op a) :
      ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) :=
    T.scheme.toRingedSpace.isUnit_res_basicOpen a
  have hcoe : (id (T.scheme.presheaf.map (homOfLE hWV).op a) :
        ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) ^ n *
      (y : ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) =
      (DividedPowerStructure.restrict T.ideal (homOfLE hWV).op x :
        ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) := by
    have h : (id (T.scheme.presheaf.map (homOfLE hWV).op (a ^ n)) :
          ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) *
        (y : ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) =
        (DividedPowerStructure.restrict T.ideal (homOfLE hWV).op x :
          ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) :=
      congrArg (fun w : ↥(sectionIdeal T.scheme.sheaf T.ideal
        (op (T.scheme.basicOpen a))) ↦ (w : ↑(T.scheme.sheaf.obj.obj
          (op (T.scheme.basicOpen a))))) hx
    rwa [map_pow] at h
  have hy : (y : ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) =
      ((u⁻¹ : _) ^ n : ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) •
        (DividedPowerStructure.restrict T.ideal (homOfLE hWV).op x :
          ↑(T.scheme.sheaf.obj.obj (op (T.scheme.basicOpen a)))) := by
    rw [← hcoe, smul_eq_mul, ← mul_assoc, ← hu, ← mul_pow,
      Units.inv_mul, one_pow, one_mul]
  rw [hy]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self x))

/-- **Every divided power relation over a basic open of `V` is killed by the quotient map.**
The relations at the restrictions of the sections over `V` are, and the relations at an element
of the span of a set are determined by the relations at the members of that set. -/
theorem dpRelationSection_mem_kernel (V : T.scheme.Opens) (hV : IsAffineOpen (dpTop T V))
    (U : V.toScheme.Opens) (a : ↑Γ(T.scheme, dpTop T V))
    (hU : V.ι ''ᵁ U = T.scheme.basicOpen a)
    (y : ↥(sectionIdeal T.scheme.sheaf T.ideal (op (V.ι ''ᵁ U)))) (m : ℕ) :
    dpRelationSection T Y f (V.ι ''ᵁ U) y m ∈ dpPresentationKernel T Y f V U := by
  refine dpRelation_mem_of_mem_span
    (fun b c ↦ (Scheme.Hom.universalRelativeDerivation f).d_mul (X := op (V.ι ''ᵁ U)) b c)
    (dpPresentationKernel T Y f V U)
    (S := Set.range fun x : ↥(sectionIdeal T.scheme.sheaf T.ideal (op (dpTop T V))) ↦
      (DividedPowerStructure.restrict T.ideal (homOfLE (image_le_dpTop V U)).op x :
        ↑(T.scheme.sheaf.obj.obj (op (V.ι ''ᵁ U)))))
    ?_ ?_ (sectionIdeal_mem_span T V hV a hU (image_le_dpTop V U) y) m
  · rintro _ ⟨x, rfl⟩
    exact (DividedPowerStructure.restrict T.ideal (homOfLE (image_le_dpTop V U)).op x).2
  · rintro _ ⟨x, rfl⟩ k
    have hmem := dpRelationRestricted_mem_kernel T Y f V U (x, k)
    rwa [show (dpRelationRestrictedSection T Y f V U (x, k)).1 =
        dpRelationSection T Y f (V.ι ''ᵁ U)
          (DividedPowerStructure.restrict T.ideal (homOfLE (image_le_dpTop V U)).op x) k from
      map_dpRelationSection T Y f (homOfLE (image_le_dpTop V U)).op x k] at hmem

/-- The span of the relations over a basic open of `V` is killed by the quotient map. -/
theorem dpRelationSpan_le_kernel (V : T.scheme.Opens) (hV : IsAffineOpen (dpTop T V))
    (U : V.toScheme.Opens) (a : ↑Γ(T.scheme, dpTop T V))
    (hU : V.ι ''ᵁ U = T.scheme.basicOpen a) :
    dpRelationSpan T Y f (V.ι ''ᵁ U) ≤ dpPresentationKernel T Y f V U := by
  refine Submodule.span_le.mpr ?_
  rintro _ ⟨⟨y, m⟩, rfl⟩
  exact dpRelationSection_mem_kernel T Y f V hV U a hU y m

/-- **The subsheaf of divided power relations dies in the cokernel of the presentation.**  A
section of the subsheaf is locally a combination of relations, and over a basic open of the
affine open `V` every relation is a combination of the restrictions of the relations over `V`,
because the divided power ideal is quasi-coherent. -/
theorem dpPresentation_relation_vanish (V : T.scheme.Opens)
    (hV : IsAffineOpen (dpTop T V)) :
    (dpRestrict T V).map (dpRelationSubmodule T Y f).ι ≫
      cokernel.π (dpPresentation T Y f V) = 0 := by
  ext U s
  show ((cokernel.π (dpPresentation T Y f V)).val.app (op U)).hom (id s.1) = 0
  refine hom_app_eq_zero_of_local (cokernel.π (dpPresentation T Y f V)) fun p hp ↦ ?_
  obtain ⟨Z, hZle, hpZ, hZmem⟩ := s.2 (V.ι.base p) ⟨p, hp, rfl⟩
  have hZtop : Z ≤ dpTop T V := hZle.trans (image_le_dpTop V U)
  obtain ⟨a, haZ, hpa⟩ := hV.exists_basicOpen_le (⟨V.ι.base p, hpZ⟩ : Z) (hZtop hpZ)
  have hbV : T.scheme.basicOpen a ≤ V :=
    (T.scheme.basicOpen_le a).trans (le_of_eq (dpTop_eq T V))
  have hU₁ : V.ι ''ᵁ (V.ι ⁻¹ᵁ T.scheme.basicOpen a) = T.scheme.basicOpen a := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι,
      inf_eq_right.mpr hbV]
  have hU₁le : V.ι ⁻¹ᵁ T.scheme.basicOpen a ≤ U := by
    rw [← Scheme.Hom.preimage_image_eq V.ι U]
    exact fun q hq ↦ hZle (haZ hq)
  refine ⟨V.ι ⁻¹ᵁ T.scheme.basicOpen a, hU₁le, hpa, ?_⟩
  change ((cokernel.π (dpPresentation T Y f V)).val.app _).hom
    (((dpRestrict T V).obj (Scheme.Hom.relativeDifferentials f)).val.map (homOfLE hU₁le).op
      (id s.1)) = 0
  have hspan : (Scheme.Hom.relativeDifferentials f).val.map
      (homOfLE (Scheme.Hom.image_mono V.ι hU₁le)).op s.1 ∈
      dpRelationSpan T Y f (V.ι ''ᵁ (V.ι ⁻¹ᵁ T.scheme.basicOpen a)) :=
    dpRelationSpan_map_map T Y f hZle ((le_of_eq hU₁).trans haZ) hZmem
  have hker := dpRelationSpan_le_kernel T Y f V hV (V.ι ⁻¹ᵁ T.scheme.basicOpen a) a hU₁ hspan
  exact (mem_dpPresentationKernel T Y f V _).1 hker

/-- The presentation dies in the cokernel of the relation subsheaf. -/
theorem dpPresentation_comp_π (V : T.scheme.Opens) :
    dpPresentation T Y f V ≫
      cokernel.π ((dpRestrict T V).map (dpRelationSubmodule T Y f).ι) = 0 := by
  rw [dpPresentation, Category.assoc, cokernel.condition, comp_zero]

/-- The two cokernels agree. -/
def dpCokernelIso (V : T.scheme.Opens) (hV : IsAffineOpen (dpTop T V)) :
    cokernel ((dpRestrict T V).map (dpRelationSubmodule T Y f).ι) ≅
      cokernel (dpPresentation T Y f V) where
  hom := cokernel.desc _ (cokernel.π (dpPresentation T Y f V))
    (dpPresentation_relation_vanish T Y f V hV)
  inv := cokernel.desc _ (cokernel.π ((dpRestrict T V).map (dpRelationSubmodule T Y f).ι))
    (dpPresentation_comp_π T Y f V)
  hom_inv_id := by
    refine (cancel_epi (cokernel.π ((dpRestrict T V).map
      (dpRelationSubmodule T Y f).ι))).1 ?_
    simp
  inv_hom_id := by
    refine (cancel_epi (cokernel.π (dpPresentation T Y f V))).1 ?_
    simp

/-- The restriction of the quotient to an affine open is quasi-coherent. -/
theorem restrict_dpQuotient_isQuasicoherent (V : T.scheme.affineOpens) :
    ((dpRestrict T (V : T.scheme.Opens)).obj (dpQuotient T Y f)).IsQuasicoherent := by
  have hV : IsAffineOpen (dpTop T (V : T.scheme.Opens)) := by
    rw [dpTop_eq]
    exact V.2
  have hfree : (dpFree T (V : T.scheme.Opens)).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.AffineQcohEquivalence.isQuasicoherent_free _
  have hΩ : ((dpRestrict T (V : T.scheme.Opens)).obj
      (Scheme.Hom.relativeDifferentials f)).IsQuasicoherent := inferInstance
  have hcok : (cokernel (dpPresentation T Y f (V : T.scheme.Opens))).IsQuasicoherent :=
    Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_cokernel _
  exact (SheafOfModules.isQuasicoherent
      (V : T.scheme.Opens).toScheme.ringCatSheaf).prop_of_iso
    (PreservesCokernel.iso (dpRestrict T (V : T.scheme.Opens))
        (dpRelationSubmodule T Y f).ι ≪≫
      dpCokernelIso T Y f (V : T.scheme.Opens) hV).symm hcok

/-- The quotient of the relative differentials by the divided power relations is
quasi-coherent. -/
instance dpQuotient_isQuasicoherent : (dpQuotient T Y f).IsQuasicoherent :=
  Stacks.AlgebraicGeometry.QuasicoherentColimits.isQuasicoherent_of_restrict_affineOpens _
    (fun V ↦ restrict_dpQuotient_isQuasicoherent T Y f V)

/-- **The sheaf of divided power differentials is quasi-coherent**, being the quotient of the
quasi-coherent sheaf of relative differentials by a subsheaf which, over an affine open, is the
image of a free module. -/
@[stacks 07IY "quasi-coherence of the sheaf of divided power differentials"]
instance dpDifferentialsSheaf_isQuasicoherent :
    (dpDifferentialsSheaf T Y f).IsQuasicoherent :=
  (SheafOfModules.isQuasicoherent T.scheme.ringCatSheaf).prop_of_iso
    (dpDifferentialsIsoQuotient T Y f).symm (dpQuotient_isQuasicoherent T Y f)

end Affine

end Crystalline

end
