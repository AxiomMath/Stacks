module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.CompactlySupportedCohomology
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.IntegralCohomologicalDimension
import StacksCore.Tactic.EgaSgaAttribute

/-!
# Extension by zero of a torsion sheaf of modules is torsion

Let `j : U ⟶ X` be an étale morphism of schemes and `Λ` a ring. Extension by zero `j_!` of
sheaves of `Λ`-modules on the small étale sites carries torsion sheaves (sections locally
annihilated by positive integers, `Stacks.EtaleCohomology.IsTorsionEtaleModule`) to torsion
sheaves. This is the input of [Stacks, Tag 0G2A] for `D⁺_tors` with an arbitrary coefficient ring:
`Rf_!` restricted to `D⁺_tors` is `R(fbar)_*` of extensions by zero of torsion sheaves.

## Main results

* `Stacks.EtaleCohomology.isLocallyTorsionModulePresheaf_leftKanExtension`: the left Kan extension
  of a locally torsion presheaf of modules along the opposite of a cover-preserving functor is
  locally torsion.
* `Stacks.EtaleCohomology.isTorsionEtaleModule_etaleModuleExtensionByZero_obj`: extension by zero
  of a torsion sheaf of modules is torsion.

## Implementation notes

The proof works for an arbitrary cover-preserving functor of sites `G` and the sheafified left Kan
extension along `G.op`, which is how `j_!` is constructed
(`Stacks.EtaleCohomology.etaleModuleExtensionByZero`). A colimit of modules is spanned by the
images of its coprojections, so every section of the left Kan extension over `U'` is a finite
linear combination of images, along arrows `U' ⟶ G V`, of sections of the original presheaf over
`V`. Such an image is locally torsion because the torsion sieve of the original section covers
and `G` preserves covers. The locally torsion sections form a submodule, so every section of the
left Kan extension is locally torsion. Sheafification is locally surjective, so it preserves
local torsion.

Unlike `Stacks.Torsion.isLocallyTorsion_lan_obj` (abelian sheaves, used for étale inverse image),
no filteredness of the comma categories is needed: the comma categories of `j_!` need not be
filtered (they are empty over étale `X`-schemes not mapping to `U`), and the linear-span
description of colimits of modules replaces the representation of elements of a filtered
colimit.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry

namespace Stacks.EtaleCohomology

universe w v₁ v₂ v₃ u₁ u₂ u r

section Span

variable {R : Type w} [Ring R] {I : Type u₁} [Category.{v₁} I]

/-- **A colimit of modules is spanned by the images of its coprojections.** The quotient by that
span kills every coprojection, hence is zero by the uniqueness of maps out of a colimit. -/
theorem span_iUnion_range_colimit_ι_eq_top (F : I ⥤ ModuleCat.{v₂} R) [HasColimit F] :
    Submodule.span R (⋃ i, Set.range (colimit.ι F i)) = ⊤ := by
  let M : ModuleCat.{v₂} R := colimit F
  let N : Submodule R M := Submodule.span R (⋃ i, Set.range (colimit.ι F i))
  let q : M ⟶ ModuleCat.of R (M ⧸ N) := ModuleCat.ofHom N.mkQ
  have hq : q = 0 := by
    refine colimit.hom_ext fun i => ?_
    ext y
    simp only [comp_zero, ModuleCat.hom_comp, LinearMap.coe_comp, Function.comp_apply,
      ModuleCat.hom_zero, LinearMap.zero_apply, q, ModuleCat.hom_ofHom]
    rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact Submodule.subset_span (Set.mem_iUnion.2 ⟨i, y, rfl⟩)
  rw [eq_top_iff]
  intro x _
  have h : N.mkQ x = 0 := by
    change q.hom x = 0
    rw [hq]
    rfl
  exact (Submodule.Quotient.mk_eq_zero N).1 h

end Span

section Presheaf

variable {C : Type u₁} [Category.{v₁} C] (J : GrothendieckTopology C) {R : Type w} [Ring R]

/-- A presheaf of `R`-modules is **locally torsion** when every section is, on the members of
some covering sieve, annihilated by a positive integer. For the underlying presheaf of a sheaf of
modules on the small étale site this is `Stacks.EtaleCohomology.IsTorsionEtaleModule`. -/
@[sga "4 IX 1.1"]
def IsLocallyTorsionModulePresheaf (P : Cᵒᵖ ⥤ ModuleCat.{v₂} R) : Prop :=
  ∀ (U : C) (x : P.obj (op U)), ∃ S : Sieve U, S ∈ J U ∧
    ∀ (V : C) (f : V ⟶ U), S f → ∃ n : ℕ, 0 < n ∧ n • P.map f.op x = 0

variable {J}

/-- The sieve of arrows along which a section of a presheaf of modules is annihilated by a
positive integer. -/
def moduleTorsionSieve (P : Cᵒᵖ ⥤ ModuleCat.{v₂} R) {U : C} (x : P.obj (op U)) : Sieve U where
  arrows V f := ∃ n : ℕ, 0 < n ∧ n • P.map f.op x = 0
  downward_closed := by
    rintro V W f ⟨n, hn, h⟩ g
    refine ⟨n, hn, ?_⟩
    rw [op_comp, P.map_comp, ModuleCat.comp_apply, ← map_nsmul, h, map_zero]

variable (J) in
/-- The locally torsion sections of a presheaf of modules over an object form a submodule. -/
def locallyTorsionSubmodule (P : Cᵒᵖ ⥤ ModuleCat.{v₂} R) (U : C) :
    Submodule R (P.obj (op U)) where
  carrier := {x | moduleTorsionSieve P x ∈ J U}
  zero_mem' := J.superset_covering (fun V f _ => ⟨1, one_pos, by simp⟩) (J.top_mem U)
  add_mem' {x y} hx hy := by
    refine J.superset_covering ?_ (J.intersection_covering hx hy)
    rintro V f ⟨⟨n, hn, hx'⟩, ⟨m, hm, hy'⟩⟩
    refine ⟨n * m, Nat.mul_pos hn hm, ?_⟩
    have h1 : (n * m) • P.map f.op x = 0 := by rw [mul_comm, ← smul_smul, hx', smul_zero]
    have h2 : (n * m) • P.map f.op y = 0 := by rw [← smul_smul, hy', smul_zero]
    rw [map_add, smul_add, h1, h2, add_zero]
  smul_mem' c x hx := by
    refine J.superset_covering ?_ hx
    rintro V f ⟨n, hn, h⟩
    exact ⟨n, hn, by rw [map_smul, smul_comm, h, smul_zero]⟩

/-- A presheaf of modules is locally torsion exactly when every section lies in the submodule of
locally torsion sections. -/
theorem isLocallyTorsionModulePresheaf_iff (P : Cᵒᵖ ⥤ ModuleCat.{v₂} R) :
    IsLocallyTorsionModulePresheaf J P ↔
      ∀ (U : C) (x : P.obj (op U)), x ∈ locallyTorsionSubmodule J P U := by
  constructor
  · intro h U x
    obtain ⟨S, hS, hkill⟩ := h U x
    exact J.superset_covering (fun V f hf => hkill V f hf) hS
  · exact fun h U x => ⟨_, h U x, fun _ _ hf => hf⟩

/-- **Local torsion passes along a locally surjective map** of presheaves of modules. -/
theorem IsLocallyTorsionModulePresheaf.of_isLocallySurjective
    {P Q : Cᵒᵖ ⥤ ModuleCat.{v₂} R} (η : P ⟶ Q) (hη : Presheaf.IsLocallySurjective J η)
    (hP : IsLocallyTorsionModulePresheaf J P) : IsLocallyTorsionModulePresheaf J Q := by
  have := hη
  rw [isLocallyTorsionModulePresheaf_iff] at hP ⊢
  intro U y
  refine J.transitive (Presheaf.imageSieve_mem J η y) _ ?_
  intro V g hg
  obtain ⟨t, ht⟩ := hg
  refine J.superset_covering ?_ (hP V t)
  intro W h hh
  obtain ⟨n, hn, hkill⟩ := hh
  refine ⟨n, hn, ?_⟩
  have hres : Q.map (h ≫ g).op y = η.app (op W) (P.map h.op t) := by
    rw [op_comp, Q.map_comp, ModuleCat.comp_apply, ← ht, NatTrans.naturality_apply η h.op]
  rw [hres, ← map_nsmul, hkill, map_zero]

variable {D : Type u₂} [Category.{v₃} D] (K : GrothendieckTopology D) (G : C ⥤ D)

/-- **The left Kan extension of a locally torsion presheaf of modules is locally torsion.** Let
`G : C ⥤ D` carry covering sieves to covering sieves. A section of the left Kan extension along
`G.op` over `U'` is a linear combination of images, along arrows `U' ⟶ G V`, of sections of `P`
over objects `V`; each of those is locally torsion because its torsion sieve on `V` covers and its
image under `G` covers `G V`. -/
theorem isLocallyTorsionModulePresheaf_leftKanExtension (hG : CoverPreserving J K G)
    (P : Cᵒᵖ ⥤ ModuleCat.{v₂} R) [G.op.HasPointwiseLeftKanExtension P]
    (hP : IsLocallyTorsionModulePresheaf J P) :
    IsLocallyTorsionModulePresheaf K (G.op.leftKanExtension P) := by
  rw [isLocallyTorsionModulePresheaf_iff] at hP ⊢
  intro U' x
  let Q := G.op.leftKanExtension P
  let η := G.op.leftKanExtensionUnit P
  -- the images of sections of `P` along arrows `U' ⟶ G V` are locally torsion
  have hgen : ∀ (V : C) (a : U' ⟶ G.obj V) (y : P.obj (op V)),
      Q.map a.op (η.app (op V) y) ∈ locallyTorsionSubmodule K Q U' := by
    intro V a y
    refine K.superset_covering ?_ (K.pullback_stable a (hG.cover_preserve (hP V y)))
    rintro W g ⟨Z, h, k, ⟨n, hn, hkill⟩, hgk⟩
    refine ⟨n, hn, ?_⟩
    have hres : Q.map g.op (Q.map a.op (η.app (op V) y)) =
        Q.map k.op (η.app (op Z) (P.map h.op y)) := by
      rw [← ModuleCat.comp_apply, ← Q.map_comp, ← op_comp, hgk, op_comp, Q.map_comp,
        ModuleCat.comp_apply]
      congr 1
      exact (NatTrans.naturality_apply η h.op y).symm
    rw [hres, ← map_nsmul, ← map_nsmul, hkill, map_zero, map_zero]
  let e := G.op.leftKanExtensionObjIsoColimit P (op U')
  have hx : e.inv (e.hom x) = x := e.hom_inv_id_apply x
  rw [← hx]
  have hmem : e.hom x ∈ Submodule.span R
      (⋃ i, Set.range (colimit.ι (CostructuredArrow.proj G.op (op U') ⋙ P) i)) := by
    rw [span_iUnion_range_colimit_ι_eq_top]
    trivial
  suffices hsuff : ∀ z ∈ Submodule.span R
      (⋃ i, Set.range (colimit.ι (CostructuredArrow.proj G.op (op U') ⋙ P) i)),
      e.inv z ∈ locallyTorsionSubmodule K Q U' from hsuff _ hmem
  intro z hz
  induction hz using Submodule.span_induction with
  | mem z hz =>
    obtain ⟨i, y, rfl⟩ := Set.mem_iUnion.1 hz
    have h := G.op.ι_leftKanExtensionObjIsoColimit_inv P (op U') i
    have hz' : e.inv (colimit.ι (CostructuredArrow.proj G.op (op U') ⋙ P) i y) =
        Q.map i.hom.unop.op (η.app (op (unop i.left)) y) := by
      change (colimit.ι _ i ≫ e.inv) y = _
      rw [h]
      rfl
    rw [hz']
    exact hgen _ _ y
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add a b _ _ ha hb => rw [map_add]; exact Submodule.add_mem _ ha hb
  | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha

end Presheaf

section Etale

attribute [local instance] HasDerivedCategory.standard

/-- **Extension by zero of a torsion sheaf of modules is torsion.** For an étale morphism
`j : U ⟶ X` and a sheaf of `Λ`-modules `F` on `U_étale` whose sections are locally annihilated by
positive integers, the sections of `j_! F` are locally annihilated by positive integers. -/
theorem isTorsionEtaleModule_etaleModuleExtensionByZero_obj (Λ : Type) [Ring Λ]
    {U X : Scheme.{u}} (j : U ⟶ X) [Etale j] (F : EtaleModules.{u, 0} Λ U)
    (hF : IsTorsionEtaleModule.{u, 0} Λ U F) :
    IsTorsionEtaleModule.{u, 0} Λ X ((etaleModuleExtensionByZero.{u, 0} Λ j).obj F) := by
  let G := Scheme.Etale.smallEtaleCompose j
  have : X.smallEtaleTopology.WEqualsLocallyBijective (ModuleCat.{u + 1} Λ) :=
    wEqualsLocallyBijective_etaleModules.{u, 0} Λ X
  exact IsLocallyTorsionModulePresheaf.of_isLocallySurjective _
    (X.smallEtaleTopology.W_toSheafify _).isLocallySurjective
    (isLocallyTorsionModulePresheaf_leftKanExtension X.smallEtaleTopology G
      (CoverPreserving.of_isContinuous _ _ _) F.obj hF)

end Etale

end Stacks.EtaleCohomology

end
