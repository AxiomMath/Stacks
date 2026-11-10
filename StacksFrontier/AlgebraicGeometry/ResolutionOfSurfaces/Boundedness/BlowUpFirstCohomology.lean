module

public import Mathlib.AlgebraicGeometry.ProjectiveSpectrum.Basic
public import StacksFrontier.AlgebraicGeometry.Curves.GlueingSquishing.PushforwardCokernelVanishing
public import StacksFrontier.AlgebraicGeometry.F6Rank89.IdealSheafStalk
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.CoordinateBlowupSmooth
public import StacksFrontier.AlgebraicGeometry.MoreMorphisms.RegularIdealSheaf.SpreadOut
public import StacksFrontier.AlgebraicGeometry.ResolutionOfSurfaces.RationalSingularities.SpreadOutVanishing
public import StacksFrontier.CategoryTheory.Sites.Cohomology.DerivedSections.FreeYonedaSections
import StacksFrontier.AlgebraicGeometry.Cohomology.Cech.AffineVanishing

/-!
# The first cohomology of the structure sheaf of a blowup in two generators

Let `A` be an `ℕ`-graded ring and `f, g ∈ A₁` two elements of degree one such that every
homogeneous element of positive degree lies in the ideal `(f, g)`. Then `Proj A` is covered by
the two affine opens `D₊(f)` and `D₊(g)`, and `H¹(Proj A, 𝒪) = 0`: by Mayer–Vietoris this is the
surjectivity of `A_(f) ⊕ A_(g) → A_(fg)`, and an element `a / (fg)ᵏ` with `a` of degree `2k` is a
combination of the monomials `fⁱ g²ᵏ⁻ⁱ / (fg)ᵏ`, each of which lies in `A_(f)` (if `i ≤ k`) or in
`A_(g)` (if `i ≥ k`).

## Main results

* `AlgebraicGeometry.Proj.surjective_awayMap_add_awayMap`: `A_(f) ⊕ A_(g) → A_(fg)` is surjective.
* `AlgebraicGeometry.Proj.subsingleton_cohomologyPresheaf_one_top`: `H¹(Proj A, 𝒪) = 0`.

## References

* [Stacks Project, Tag 0AGS](https://stacks.math.columbia.edu/tag/0AGS)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace HomogeneousLocalization

universe u

namespace AlgebraicGeometry.Proj

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)

/-- The sum of the two localization maps `A_(f) → A_(fg)` and `A_(g) → A_(fg)`. -/
def awayMapAdd : Away 𝒜 f × Away 𝒜 g →+ Away 𝒜 (f * g) :=
  (awayMap 𝒜 hg rfl).toAddMonoidHom.coprod (awayMap 𝒜 hf (mul_comm f g)).toAddMonoidHom

include hf hg in
/-- Each fraction `a fᵖ gᵠ / (fg)ᵏ` with `a` of degree `n` and `n + p + q = 2k` lies in the image
of `A_(f) ⊕ A_(g)`, by induction on `n`: in degree zero the fraction is `a fᵖ⁻ᵏ / gᵖ⁻ᵏ` or
`a gᵠ⁻ᵏ / fᵠ⁻ᵏ`, and in positive degree `a = r f + s g` with `r, s` of degree `n - 1`. -/
theorem exists_awayMapAdd_val_eq
    (hspan : ∀ n, 0 < n → ∀ a ∈ 𝒜 n, a ∈ Ideal.span {f, g}) (n : ℕ) :
    ∀ a ∈ 𝒜 n, ∀ p q k : ℕ, n + p + q = 2 * k →
      ∃ z, (awayMapAdd 𝒜 hf hg z).val =
        (Localization.mk (a * f ^ p * g ^ q)
          ⟨(f * g) ^ k, (Submonoid.mem_powers_iff _ _).mpr ⟨k, rfl⟩⟩ :
            Localization.Away (f * g)) := by
  induction n with
  | zero =>
    intro a ha p q k hk
    rcases le_total k p with hkp | hpk
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hkp
      obtain rfl : q + e = k := by omega
      have hb : a * f ^ e ∈ 𝒜 (e • 1) := by
        simpa using SetLike.mul_mem_graded ha (SetLike.pow_mem_graded e hf)
      refine ⟨(0, Away.mk 𝒜 hg e (a * f ^ e) hb), ?_⟩
      simp only [awayMapAdd, AddMonoidHom.coprod_apply, map_zero, zero_add,
        RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
      rw [Away.mk, val_awayMap_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp only [OneMemClass.coe_one, one_mul]
      ring
    · obtain ⟨e, rfl⟩ := Nat.exists_eq_add_of_le hpk
      obtain rfl : q = p + 2 * e := by omega
      have hb : a * g ^ e ∈ 𝒜 (e • 1) := by
        simpa using SetLike.mul_mem_graded ha (SetLike.pow_mem_graded e hg)
      refine ⟨(Away.mk 𝒜 hf e (a * g ^ e) hb, 0), ?_⟩
      simp only [awayMapAdd, AddMonoidHom.coprod_apply, map_zero, add_zero,
        RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_ofClass]
      rw [Away.mk, val_awayMap_mk, Localization.mk_eq_mk_iff, Localization.r_iff_exists]
      refine ⟨1, ?_⟩
      simp only [OneMemClass.coe_one, one_mul]
      ring
  | succ n ih =>
    intro a ha p q k hk
    obtain ⟨r, s, hrs⟩ := Ideal.mem_span_pair.mp (hspan (n + 1) n.succ_pos a ha)
    have ha' : a = (DirectSum.decompose 𝒜 r n : A) * f + (DirectSum.decompose 𝒜 s n : A) * g := by
      rw [← DirectSum.decompose_of_mem_same 𝒜 ha, ← hrs, DirectSum.decompose_add,
        DirectSum.add_apply, AddMemClass.coe_add, DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 hf,
        DirectSum.coe_decompose_mul_add_of_right_mem 𝒜 hg]
    obtain ⟨z₁, hz₁⟩ := ih _ (DirectSum.decompose 𝒜 r n).2 (p + 1) q k (by omega)
    obtain ⟨z₂, hz₂⟩ := ih _ (DirectSum.decompose 𝒜 s n).2 p (q + 1) k (by omega)
    refine ⟨z₁ + z₂, ?_⟩
    rw [map_add, val_add, hz₁, hz₂, Localization.add_mk_self, ha']
    congr 1
    ring

include hf hg in
/-- **`A_(f) ⊕ A_(g) → A_(fg)` is surjective** when every homogeneous element of positive degree
lies in the ideal `(f, g)`. -/
theorem surjective_awayMapAdd
    (hspan : ∀ n, 0 < n → ∀ a ∈ 𝒜 n, a ∈ Ideal.span {f, g}) :
    Function.Surjective (awayMapAdd 𝒜 hf hg) := by
  intro w
  have hfg : f * g ∈ 𝒜 2 := by simpa using SetLike.mul_mem_graded hf hg
  obtain ⟨k, a, ha, rfl⟩ := Away.mk_surjective 𝒜 hfg w
  obtain ⟨z, hz⟩ := exists_awayMapAdd_val_eq 𝒜 hf hg hspan (k • 2) a ha 0 0 k
    (by simp [smul_eq_mul, mul_comm])
  refine ⟨z, val_injective _ ?_⟩
  rw [hz, Away.val_mk]
  simp

include hf hg in
/-- **The sections of `𝒪_{Proj A}` over `D₊(f) ∩ D₊(g)` are sums of sections over `D₊(f)` and
over `D₊(g)`**, when every homogeneous element of positive degree lies in `(f, g)`. -/
theorem exists_sections_eq_add (hspan : ∀ n, 0 < n → ∀ a ∈ 𝒜 n, a ∈ Ideal.span {f, g})
    (W : (Proj 𝒜).Opens) (hW : basicOpen 𝒜 (f * g) = W) (h₁ : W ≤ basicOpen 𝒜 f)
    (h₂ : W ≤ basicOpen 𝒜 g) (s : Γ(Proj 𝒜, W)) :
    ∃ (t₁ : Γ(Proj 𝒜, basicOpen 𝒜 f)) (t₂ : Γ(Proj 𝒜, basicOpen 𝒜 g)),
      s = (Proj 𝒜).presheaf.map (homOfLE h₁).op t₁ + (Proj 𝒜).presheaf.map (homOfLE h₂).op t₂ := by
  subst hW
  have hiso : IsIso (awayToSection 𝒜 (f * g)) :=
    (basicOpenIsoAway 𝒜 (f * g) (SetLike.mul_mem_graded hf hg) (by norm_num)).isIso_hom
  obtain ⟨w, rfl⟩ : ∃ w, (awayToSection 𝒜 (f * g)).hom w = s :=
    (ConcreteCategory.bijective_of_isIso (awayToSection 𝒜 (f * g))).2 s
  obtain ⟨⟨z₁, z₂⟩, rfl⟩ := surjective_awayMapAdd 𝒜 hf hg hspan w
  refine ⟨(awayToSection 𝒜 f).hom z₁, (awayToSection 𝒜 g).hom z₂, ?_⟩
  have e₁ := congrArg (fun φ : CommRingCat.of (Away 𝒜 f) ⟶ _ => φ.hom z₁)
    (awayMap_awayToSection 𝒜 hg (rfl : f * g = f * g))
  have e₂ := congrArg (fun φ : CommRingCat.of (Away 𝒜 g) ⟶ _ => φ.hom z₂)
    (awayMap_awayToSection 𝒜 hf (mul_comm f g : f * g = g * f))
  simp only [CommRingCat.hom_comp, RingHom.coe_comp, Function.comp_apply,
    CommRingCat.hom_ofHom] at e₁ e₂
  simp only [awayMapAdd, AddMonoidHom.coprod_apply, RingHom.toAddMonoidHom_eq_coe,
    AddMonoidHom.coe_ofClass, map_add]
  rw [e₁, e₂]

end AlgebraicGeometry.Proj

namespace AlgebraicGeometry

section MayerVietoris

variable {X : Scheme.{u}} [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) Ab.{u})]

/-- If every section of `𝒪_X` over `U ∩ V` is a sum of a section over `U` and one over `V`, the
difference map `H⁰(U) ⊕ H⁰(V) → H⁰(U ∩ V)` of the Mayer–Vietoris sequence is surjective. -/
theorem surjective_fromBiprod_zero_of_sections {U V : X.Opens}
    (hsurj : ∀ s : Γ(X, U ⊓ V), ∃ (a : Γ(X, U)) (b : Γ(X, V)),
      s = X.presheaf.map (homOfLE inf_le_left).op a + X.presheaf.map (homOfLE inf_le_right).op b) :
    Function.Surjective
      ((Opens.mayerVietorisSquare U V).fromBiprod (structureAbelianSheaf X) 0) := by
  let F := structureAbelianSheaf X
  let S := Opens.mayerVietorisSquare U V
  let e := Stacks.Cohomology.FreeYoneda.cohomologyPresheafIsoSections F
  intro z
  obtain ⟨a, b, hab⟩ := hsurj ((e.hom.app (op (U ⊓ V))) z)
  let a' : ((sheafToPresheaf _ _).obj F).obj (op U) := a
  let b' : ((sheafToPresheaf _ _).obj F).obj (op V) := b
  have hab' : (e.hom.app (op (U ⊓ V))) z = ((sheafToPresheaf _ _).obj F).map S.f₁₂.op a' +
      ((sheafToPresheaf _ _).obj F).map S.f₁₃.op b' := hab
  let y₁ : F.H' 0 S.X₂ := e.inv.app (op U) a'
  let y₂ : F.H' 0 S.X₃ := -e.inv.app (op V) b'
  refine ⟨(AddCommGrpCat.biprodIsoProd _ _).inv ⟨y₁, y₂⟩, ?_⟩
  rw [S.fromBiprod_biprodIsoProd_inv_apply]
  have n₁ : e.inv.app (op S.X₁) (((sheafToPresheaf _ _).obj F).map S.f₁₂.op a') =
      (F.cohomologyPresheaf 0).map S.f₁₂.op (e.inv.app (op S.X₂) a') :=
    NatTrans.naturality_apply e.inv S.f₁₂.op a'
  have n₂ : e.inv.app (op S.X₁) (((sheafToPresheaf _ _).obj F).map S.f₁₃.op b') =
      (F.cohomologyPresheaf 0).map S.f₁₃.op (e.inv.app (op S.X₃) b') :=
    NatTrans.naturality_apply e.inv S.f₁₃.op b'
  change (F.cohomologyPresheaf 0).map S.f₁₂.op (e.inv.app (op S.X₂) a') -
    (F.cohomologyPresheaf 0).map S.f₁₃.op (-(e.inv.app (op S.X₃) b')) = z
  rw [map_neg, sub_neg_eq_add, ← n₁, ← n₂, ← map_add, ← hab']
  exact e.hom_inv_id_app_apply _ z

/-- If `H¹(U ∪ V, 𝒪_X) = 0`, every section of `𝒪_X` over `U ∩ V` is a sum of a section over `U`
and one over `V` (Mayer–Vietoris in degree zero). -/
theorem exists_sections_eq_add_of_subsingleton {U V : X.Opens}
    (h : Subsingleton (((structureAbelianSheaf X).cohomologyPresheaf.{u} 1).obj (op (U ⊔ V))))
    (s : Γ(X, U ⊓ V)) : ∃ (a : Γ(X, U)) (b : Γ(X, V)),
      s = X.presheaf.map (homOfLE inf_le_left).op a +
        X.presheaf.map (homOfLE inf_le_right).op b := by
  let F := structureAbelianSheaf X
  let S := Opens.mayerVietorisSquare U V
  let e := Stacks.Cohomology.FreeYoneda.cohomologyPresheafIsoSections F
  let s' : ((sheafToPresheaf _ _).obj F).obj (op (U ⊓ V)) := s
  obtain ⟨t, ht⟩ := (ShortComplex.ab_exact_iff _).1 ((S.sequence_exact F 0 1 rfl).exact 1)
    (e.inv.app (op (U ⊓ V)) s') (@Subsingleton.elim _ h _ _)
  obtain ⟨⟨y₁, y₂⟩, rfl⟩ := (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm
    |>.surjective t
  change S.fromBiprod F 0 ((AddCommGrpCat.biprodIsoProd _ _).inv ⟨y₁, y₂⟩) = _ at ht
  rw [S.fromBiprod_biprodIsoProd_inv_apply] at ht
  refine ⟨e.hom.app (op U) y₁, -e.hom.app (op V) y₂, ?_⟩
  have n₁ : e.hom.app (op S.X₁) ((F.cohomologyPresheaf 0).map S.f₁₂.op y₁) =
      ((sheafToPresheaf _ _).obj F).map S.f₁₂.op (e.hom.app (op S.X₂) y₁) :=
    NatTrans.naturality_apply e.hom S.f₁₂.op y₁
  have n₂ : e.hom.app (op S.X₁) ((F.cohomologyPresheaf 0).map S.f₁₃.op y₂) =
      ((sheafToPresheaf _ _).obj F).map S.f₁₃.op (e.hom.app (op S.X₃) y₂) :=
    NatTrans.naturality_apply e.hom S.f₁₃.op y₂
  have key : s' = ((sheafToPresheaf _ _).obj F).map S.f₁₂.op (e.hom.app (op S.X₂) y₁) +
      ((sheafToPresheaf _ _).obj F).map S.f₁₃.op (-(e.hom.app (op S.X₃) y₂)) := by
    rw [map_neg, ← sub_eq_add_neg, ← n₁, ← n₂, ← map_sub, ht]
    exact (e.inv_hom_id_app_apply _ s').symm
  exact key

/-- If `H¹(V ∪ U, 𝒪_X) = 0`, the restriction `H¹(U, 𝒪_X) → H¹(V ∩ U, 𝒪_X)` is injective
(Mayer–Vietoris in degree one). -/
theorem injective_cohomologyPresheaf_one_map_of_subsingleton_sup {U V : X.Opens}
    (h : Subsingleton (((structureAbelianSheaf X).cohomologyPresheaf.{u} 1).obj (op (V ⊔ U)))) :
    Function.Injective (((structureAbelianSheaf X).cohomologyPresheaf.{u} 1).map
      (homOfLE (inf_le_right : V ⊓ U ≤ U)).op) := by
  let F := structureAbelianSheaf X
  let S := Opens.mayerVietorisSquare V U
  rw [injective_iff_map_eq_zero]
  intro b hb
  let b' : F.H' 1 S.X₃ := b
  let z' : F.H' 1 S.X₂ := 0
  have hfrom : S.fromBiprod F 1 ((AddCommGrpCat.biprodIsoProd _ _).inv ⟨z', b'⟩) = 0 := by
    rw [S.fromBiprod_biprodIsoProd_inv_apply]
    simp only [z', map_zero, zero_sub, neg_eq_zero]
    exact hb
  obtain ⟨d, hd⟩ := (ShortComplex.ab_exact_iff _).1 ((S.sequence_exact F 0 1 rfl).exact 3) _ hfrom
  obtain rfl : d = 0 := @Subsingleton.elim _ h _ _
  rw [map_zero] at hd
  have hb' : b' = 0 := by
    simpa only [Iso.inv_hom_id_apply, map_zero, Prod.snd_zero] using
      (congrArg (fun t => ((AddCommGrpCat.biprodIsoProd _ _).hom t).2) hd).symm
  exact hb'

/-- **Mayer–Vietoris.** If every section of `𝒪_X` over `U ∩ V` is a sum of a section over `U` and
one over `V`, `H¹(U, 𝒪_X) = 0` and `H¹(V, 𝒪_X) → H¹(U ∩ V, 𝒪_X)` is injective, then
`H¹(U ∪ V, 𝒪_X) = 0`. -/
theorem subsingleton_cohomologyPresheaf_one_sup_of_injective {U V : X.Opens}
    (hsurj : ∀ s : Γ(X, U ⊓ V), ∃ (a : Γ(X, U)) (b : Γ(X, V)),
      s = X.presheaf.map (homOfLE inf_le_left).op a + X.presheaf.map (homOfLE inf_le_right).op b)
    (hU : Subsingleton (((structureAbelianSheaf X).cohomologyPresheaf.{u} 1).obj (op U)))
    (hinj : Function.Injective (((structureAbelianSheaf X).cohomologyPresheaf.{u} 1).map
      (homOfLE (inf_le_right : U ⊓ V ≤ V)).op)) :
    Subsingleton (((structureAbelianSheaf X).cohomologyPresheaf.{u} 1).obj (op (U ⊔ V))) := by
  let F := structureAbelianSheaf X
  let S := Opens.mayerVietorisSquare U V
  refine subsingleton_of_forall_eq 0 fun c₀ => ?_
  let c : F.H' 1 S.X₄ := c₀
  suffices hc0 : c = 0 from hc0
  have hto : S.toBiprod F 1 c = 0 := by
    have hc : S.fromBiprod F 1 (S.toBiprod F 1 c) = 0 := by
      rw [← ConcreteCategory.comp_apply, S.toBiprod_fromBiprod]
      rfl
    rw [S.toBiprod_apply] at hc ⊢
    rw [S.fromBiprod_biprodIsoProd_inv_apply] at hc
    have ha : (F.cohomologyPresheaf 1).map S.f₂₄.op c = 0 := @Subsingleton.elim _ hU _ _
    rw [ha, map_zero, zero_sub, neg_eq_zero] at hc
    rw [ha, hinj (hc.trans (map_zero _).symm)]
    exact (AddCommGrpCat.biprodIsoProd _ _).addCommGroupIsoToAddEquiv.symm.map_zero
  obtain ⟨s, hs⟩ := (ShortComplex.ab_exact_iff _).1 ((S.sequence_exact F 0 1 rfl).exact 2) c hto
  obtain ⟨t, rfl⟩ := surjective_fromBiprod_zero_of_sections hsurj s
  rw [← hs]
  exact ConcreteCategory.congr_hom (S.fromBiprod_δ F 0 1 rfl) t

/-- **Mayer–Vietoris for two affine opens.** If `U` and `V` are affine opens of a scheme `X` and
every section of `𝒪_X` over `U ∩ V` is a sum of a section over `U` and a section over `V`, then
`H¹(U ∪ V, 𝒪_X) = 0`. -/
theorem subsingleton_cohomologyPresheaf_one_sup_of_isAffineOpen
    {U V : X.Opens} (hU : IsAffineOpen U) (hV : IsAffineOpen V)
    (hsurj : ∀ s : Γ(X, U ⊓ V), ∃ (a : Γ(X, U)) (b : Γ(X, V)),
      s = X.presheaf.map (homOfLE inf_le_left).op a + X.presheaf.map (homOfLE inf_le_right).op b) :
    Subsingleton (((structureAbelianSheaf X).cohomologyPresheaf.{u} 1).obj (op (U ⊔ V))) := by
  have hvan : ∀ W : X.Opens, IsAffineOpen W →
      Subsingleton (((structureAbelianSheaf X).cohomologyPresheaf.{u} 1).obj (op W)) :=
    fun W hW => AddCommGrpCat.subsingleton_of_isZero
      ((Stacks.Cohomology.AffineCover.isZero_hgroup_iff_isZero_cohomologyPresheaf W _ 1).1
        (Stacks.Cohomology.Cech.isZero_hgroup_of_isAffineOpen X
          (SheafOfModules.unit X.ringCatSheaf) W hW 1 one_pos))
  exact subsingleton_cohomologyPresheaf_one_sup_of_injective hsurj (hvan U hU)
    fun a b _ => @Subsingleton.elim _ (hvan V hV) a b

end MayerVietoris

namespace Proj

variable {σ : Type*} {A : Type u} [CommRing A] [SetLike σ A] [AddSubgroupClass σ A]
  (𝒜 : ℕ → σ) [GradedRing 𝒜] {f g : A} (hf : f ∈ 𝒜 1) (hg : g ∈ 𝒜 1)

/-- `D₊(f)` and `D₊(g)` cover `Proj A` when every homogeneous element of positive degree lies in
`(f, g)`. -/
theorem basicOpen_sup_basicOpen_eq_top
    (hspan : ∀ n, 0 < n → ∀ a ∈ 𝒜 n, a ∈ Ideal.span {f, g}) :
    basicOpen 𝒜 f ⊔ basicOpen 𝒜 g = ⊤ := by
  rw [← iSup_basicOpen_eq_top 𝒜 ![f, g] (by
    rw [HomogeneousIdeal.irrelevant_eq_span, Ideal.span_le]
    intro z hz
    obtain ⟨n, hn, hzn⟩ := Set.mem_iUnion₂.mp hz
    rw [Matrix.range_cons_cons_empty]
    exact hspan n hn z hzn)]
  apply le_antisymm
  · exact sup_le (le_iSup (fun i => basicOpen 𝒜 (![f, g] i)) 0)
      (le_iSup (fun i => basicOpen 𝒜 (![f, g] i)) 1)
  · refine iSup_le fun i => ?_
    fin_cases i
    exacts [le_sup_left, le_sup_right]

include hf hg in
/-- **`H¹(Proj A, 𝒪) = 0`** for an `ℕ`-graded ring `A` all of whose homogeneous elements of
positive degree lie in the ideal generated by two elements `f, g` of degree one. -/
theorem subsingleton_cohomologyPresheaf_one_top
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology (Proj 𝒜)) Ab.{u})]
    (hspan : ∀ n, 0 < n → ∀ a ∈ 𝒜 n, a ∈ Ideal.span {f, g}) :
    Subsingleton (((structureAbelianSheaf (Proj 𝒜)).cohomologyPresheaf.{u} 1).obj
      (op (⊤ : (Proj 𝒜).Opens))) := by
  rw [← basicOpen_sup_basicOpen_eq_top 𝒜 hspan]
  exact subsingleton_cohomologyPresheaf_one_sup_of_isAffineOpen
    (isAffineOpen_basicOpen 𝒜 f hf one_pos) (isAffineOpen_basicOpen 𝒜 g hg one_pos)
    (exists_sections_eq_add 𝒜 hf hg hspan _ (basicOpen_mul 𝒜 f g) inf_le_left inf_le_right)

end Proj

/-- Abelian sheaves on the opens of a scheme have `Ext` groups, as there are enough injectives. -/
private theorem hasExt_sheaf_opens_ab (X : Scheme.{u}) :
    HasExt.{u} (Sheaf (Opens.grothendieckTopology X) Ab.{u}) :=
  haveI : EnoughInjectives (Sheaf (Opens.grothendieckTopology X) Ab.{u}) :=
    IsGrothendieckAbelian.enoughInjectives
  hasExt_of_enoughInjectives _

/-- **`H¹ = 0` over an affine open where the centre has two generators.** Let `I` be a
quasi-coherent ideal sheaf on a scheme `X` and `V` an affine open of `X` on which `I` is generated
by two sections `x, y`. Then the part `b⁻¹(V)` of the blowup lying over `V` has
`H¹(b⁻¹(V), 𝒪) = 0`: it is the `Proj` of the Rees algebra of `I(V)`, which is generated in degree
one by `x` and `y`. -/
theorem subsingleton_cohomologyPresheaf_one_preimage_blowUp {X : Scheme.{u}}
    (I : X.IdealSheafData) (V : X.affineOpens) (x y : Γ(X, V.1))
    (hxy : I.ideal V = Ideal.span {x, y})
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology (blowUp I)) Ab.{u})] :
    Subsingleton (((structureAbelianSheaf (blowUp I)).cohomologyPresheaf.{u} 1).obj
      (op (blowUpToBase I ⁻¹ᵁ V.1))) := by
  let c := (reesSituation I).relativeProjChart V
  have hpb := (reesSituation I).relativeProjChart_isPullback V
  have hrange : c ''ᵁ ⊤ = blowUpToBase I ⁻¹ᵁ V.1 := by
    have : HasPullback (blowUpToBase I) V.1.ι := hpb.hasPullback
    calc c ''ᵁ ⊤ = c.opensRange := Scheme.Hom.image_top_eq_opensRange c
      _ = (hpb.isoPullback.hom ≫ pullback.fst (blowUpToBase I) V.1.ι).opensRange := by
          simp only [hpb.isoPullback_hom_fst]
          rfl
      _ = (pullback.fst (blowUpToBase I) V.1.ι).opensRange :=
          Scheme.Hom.opensRange_comp_of_isIso _ _
      _ = blowUpToBase I ⁻¹ᵁ V.1.ι.opensRange := Scheme.Hom.opensRange_pullbackFst _ _
      _ = blowUpToBase I ⁻¹ᵁ V.1 := by rw [Scheme.Opens.opensRange_ι]
  have hx : x ∈ I.ideal V := hxy ▸ Ideal.subset_span (by simp)
  have hy : y ∈ I.ideal V := hxy ▸ Ideal.subset_span (by simp)
  let P := (reesSituation I).sectionRingGrading V.1
  have hspan : ∀ n, 0 < n → ∀ a ∈ P n, a ∈ Ideal.span
      {(reesDegreeOne I V ⟨x, hx⟩).1, (reesDegreeOne I V ⟨y, hy⟩).1} := by
    intro n hn a ha
    refine rees_homogeneous_mem_ideal I V _ (fun b => ?_) n hn a ha
    refine reesDegreeOne_mem_of_span I V ![x, y] (fun j => by fin_cases j <;> assumption)
      (by
        rw [hxy, Ideal.span_le]
        rintro z (rfl | rfl)
        exacts [Ideal.subset_span ⟨0, rfl⟩, Ideal.subset_span ⟨1, rfl⟩]) _ (fun j => ?_) b
    fin_cases j <;> exact Ideal.subset_span (by simp)
  have := hasExt_sheaf_opens_ab (Proj P)
  have h := Proj.subsingleton_cohomologyPresheaf_one_top P (reesDegreeOne I V ⟨x, hx⟩).2
    (reesDegreeOne I V ⟨y, hy⟩).2 hspan
  rw [← hrange]
  exact ((c.structureSheafCohomologyPresheafIso.{u} 1).app (op ⊤)).addCommGroupIsoToAddEquiv
    |>.toEquiv.subsingleton

/-- Restriction maps of a presheaf on a preorder between equal pairs of objects are injective
together. -/
theorem injective_map_homOfLE_congr {T : Type*} [Preorder T] (F : Tᵒᵖ ⥤ AddCommGrpCat.{u})
    {a b a' b' : T} (ha : a = a') (hb : b = b') (h : a ≤ b) (h' : a' ≤ b') :
    Function.Injective (F.map (homOfLE h).op) ↔ Function.Injective (F.map (homOfLE h').op) := by
  subst ha hb
  rfl

/-- **Injectivity of `H¹(U, 𝒪) → H¹(V ∩ U, 𝒪)` passes up along a morphism which is an isomorphism
over `U`.** If `g : X' ⟶ X` is an isomorphism over `U`, the injectivity of the restriction
`H¹(U, 𝒪_X) → H¹(V ∩ U, 𝒪_X)` gives that of `H¹(g⁻¹ U, 𝒪_{X'}) → H¹(g⁻¹ V ∩ g⁻¹ U, 𝒪_{X'})`. -/
theorem injective_cohomologyPresheaf_one_map_preimage_of_isIso_morphismRestrict
    {X X' : Scheme.{u}} [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) Ab.{u})]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X') Ab.{u})]
    (g : X' ⟶ X) (U V : X.Opens) [IsIso (g ∣_ U)]
    (hinjX : Function.Injective (((structureAbelianSheaf X).cohomologyPresheaf.{u} 1).map
      (homOfLE (inf_le_right : V ⊓ U ≤ U)).op)) :
    Function.Injective (((structureAbelianSheaf X').cohomologyPresheaf.{u} 1).map
      (homOfLE (inf_le_right : g ⁻¹ᵁ V ⊓ g ⁻¹ᵁ U ≤ g ⁻¹ᵁ U)).op) := by
  let P := (structureAbelianSheaf X).cohomologyPresheaf.{u} 1
  let P' := (structureAbelianSheaf X').cohomologyPresheaf.{u} 1
  let h : U.toScheme ⟶ X' := inv (g ∣_ U) ≫ (g ⁻¹ᵁ U).ι
  have := hasExt_sheaf_opens_ab U.toScheme
  let α := (U.ι.structureSheafCohomologyPresheafIso.{u} 1) ≪≫
    (h.structureSheafCohomologyPresheafIso.{u} 1).symm
  have hle : U.ι ⁻¹ᵁ V ≤ ⊤ := le_top
  have e₁ : U.ι ''ᵁ (U.ι ⁻¹ᵁ V) = V ⊓ U := by
    rw [Scheme.Hom.image_preimage_eq_opensRange_inf, Scheme.Opens.opensRange_ι, inf_comm]
  have e₂ : U.ι ''ᵁ ⊤ = U := by
    rw [Scheme.Hom.image_top_eq_opensRange, Scheme.Opens.opensRange_ι]
  have hinjU : Function.Injective (P.map (U.ι.opensFunctor.map (homOfLE hle)).op) :=
    (injective_map_homOfLE_congr P e₁ e₂ (U.ι.image_mono hle) inf_le_right).2 hinjX
  have hinjU' : Function.Injective (P'.map (h.opensFunctor.map (homOfLE hle)).op) := by
    have hcomp : (α.inv.app (op ⊤) ≫ P.map (U.ι.opensFunctor.map (homOfLE hle)).op) ≫
        α.hom.app (op (U.ι ⁻¹ᵁ V)) = P'.map (h.opensFunctor.map (homOfLE hle)).op := by
      rw [Category.assoc]
      exact (congrArg (fun k => α.inv.app (op ⊤) ≫ k) (α.hom.naturality (homOfLE hle).op)).trans
        (α.inv_hom_id_app_assoc _ _)
    rw [← hcomp]
    exact ((ConcreteCategory.bijective_of_isIso (α.hom.app (op (U.ι ⁻¹ᵁ V)))).1.comp
      hinjU).comp (ConcreteCategory.bijective_of_isIso (α.inv.app (op ⊤))).1
  have f₁ : h ''ᵁ (U.ι ⁻¹ᵁ V) = g ⁻¹ᵁ V ⊓ g ⁻¹ᵁ U := by
    rw [image_inv_morphismRestrict_ι, Scheme.Hom.image_preimage_eq_opensRange_inf,
      Scheme.Opens.opensRange_ι, Scheme.Hom.preimage_inf, inf_comm]
  have f₂ : h ''ᵁ ⊤ = g ⁻¹ᵁ U := by
    rw [image_inv_morphismRestrict_ι, Scheme.Hom.image_top_eq_opensRange,
      Scheme.Opens.opensRange_ι]
  exact (injective_map_homOfLE_congr P' f₁ f₂ (h.image_mono hle) inf_le_right).1 hinjU'

/-- **Splitting of sections passes up along a morphism which is an isomorphism over `U`.** If
`g : X' ⟶ X` is an isomorphism over `U` and every section of `𝒪_X` over `V ∩ U` is a sum of a
section over `V` and one over `U`, the same holds on `X'` for `g⁻¹ V` and `g⁻¹ U`. -/
theorem exists_sections_preimage_eq_add_of_isIso_morphismRestrict {X X' : Scheme.{u}}
    (g : X' ⟶ X) (U V : X.Opens) [IsIso (g ∣_ U)]
    (hsec : ∀ s : Γ(X, V ⊓ U), ∃ (a : Γ(X, V)) (b : Γ(X, U)),
      s = X.presheaf.map (homOfLE inf_le_left).op a + X.presheaf.map (homOfLE inf_le_right).op b)
    (s : Γ(X', g ⁻¹ᵁ V ⊓ g ⁻¹ᵁ U)) : ∃ (a : Γ(X', g ⁻¹ᵁ V)) (b : Γ(X', g ⁻¹ᵁ U)),
      s = X'.presheaf.map (homOfLE inf_le_left).op a +
        X'.presheaf.map (homOfLE inf_le_right).op b := by
  have := Stacks.GlueSquishFactor.isIso_app_of_isIso_morphismRestrict g U (V ⊓ U) inf_le_right
  have hpre : g ⁻¹ᵁ (V ⊓ U) = g ⁻¹ᵁ V ⊓ g ⁻¹ᵁ U := g.preimage_inf
  obtain ⟨σ, hσ⟩ := (ConcreteCategory.bijective_of_isIso (g.app (V ⊓ U))).2
    (X'.presheaf.map (eqToHom hpre).op s)
  obtain ⟨a, b, hab⟩ := hsec σ
  refine ⟨g.app V a, g.app U b, ?_⟩
  have nat : ∀ {T : X.Opens} (i : V ⊓ U ⟶ T) (c : Γ(X, T)),
      g.app (V ⊓ U) (X.presheaf.map i.op c) =
        X'.presheaf.map ((Opens.map g.base).map i).op (g.app T c) := fun i c => by
    rw [← ConcreteCategory.comp_apply, Scheme.Hom.naturality]
    rfl
  have key : X'.presheaf.map (eqToHom hpre).op s =
      X'.presheaf.map (eqToHom hpre).op (X'.presheaf.map (homOfLE inf_le_left).op (g.app V a) +
        X'.presheaf.map (homOfLE inf_le_right).op (g.app U b)) := by
    rw [← hσ, hab, map_add, nat, nat, map_add]
    congr 1 <;>
    · conv_rhs => rw [← ConcreteCategory.comp_apply, ← Functor.map_comp]
      rfl
  exact (ConcreteCategory.bijective_of_isIso (X'.presheaf.map (eqToHom hpre).op)).1 key

/-- **The vanishing of `H¹(𝒪)` passes up along a morphism which is an isomorphism over `U`.**
Let `g : X' ⟶ X` be an isomorphism over an open `U`, and `V` an open with `V ∪ U = X`. If
`H¹(X, 𝒪) = 0` and `H¹(g⁻¹ V, 𝒪) = 0`, then `H¹(X', 𝒪) = 0`.

On `X` the Mayer–Vietoris sequence for `X = V ∪ U` makes `Γ(V) ⊕ Γ(U) → Γ(V ∩ U)` surjective and
`H¹(U) → H¹(V ∩ U)` injective; `g` carries both statements to `g⁻¹ V` and `g⁻¹ U`, and the
Mayer–Vietoris sequence for `X' = g⁻¹ V ∪ g⁻¹ U` then forces `H¹(X') = 0`. -/
theorem subsingleton_cohomologyPresheaf_one_top_of_isIso_morphismRestrict {X X' : Scheme.{u}}
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X) Ab.{u})]
    [HasExt.{u} (Sheaf (Opens.grothendieckTopology X') Ab.{u})]
    (g : X' ⟶ X) (U V : X.Opens) (hUV : V ⊔ U = ⊤) [IsIso (g ∣_ U)]
    (hX : Subsingleton (((structureAbelianSheaf X).cohomologyPresheaf.{u} 1).obj
      (op (⊤ : X.Opens))))
    (hV' : Subsingleton (((structureAbelianSheaf X').cohomologyPresheaf.{u} 1).obj
      (op (g ⁻¹ᵁ V)))) :
    Subsingleton (((structureAbelianSheaf X').cohomologyPresheaf.{u} 1).obj
      (op (⊤ : X'.Opens))) := by
  have hX₄ : Subsingleton (((structureAbelianSheaf X).cohomologyPresheaf.{u} 1).obj
      (op (V ⊔ U))) := by
    rwa [hUV]
  have htop : g ⁻¹ᵁ V ⊔ g ⁻¹ᵁ U = ⊤ := by
    rw [← Scheme.Hom.preimage_sup, hUV, Scheme.Hom.preimage_top]
  rw [← htop]
  exact subsingleton_cohomologyPresheaf_one_sup_of_injective
    (exists_sections_preimage_eq_add_of_isIso_morphismRestrict g U V
      (exists_sections_eq_add_of_subsingleton hX₄)) hV'
    (injective_cohomologyPresheaf_one_map_preimage_of_isIso_morphismRestrict g U V
      (injective_cohomologyPresheaf_one_map_of_subsingleton_sup hX₄))

/-- The maximal ideal of a regular local ring of dimension two is generated by a regular sequence
of length two. -/
theorem exists_span_pair_eq_maximalIdeal_isRegular (R : Type*) [CommRing R] [IsRegularLocalRing R]
    (hdim : ringKrullDim R = 2) : ∃ x y : R, Ideal.span {x, y} = IsLocalRing.maximalIdeal R ∧
      RingTheory.Sequence.IsRegular R [x, y] := by
  classical
  obtain ⟨sA, hsAcard, hsAspan⟩ :=
    Submodule.FG.exists_span_finset_card_eq_spanFinrank
      (IsLocalRing.maximalIdeal R).fg_of_isNoetherianRing
  have hsf : (IsLocalRing.maximalIdeal R).spanFinrank = 2 := by
    have h := IsRegularLocalRing.spanFinrank_maximalIdeal (R := R)
    rw [hdim] at h
    exact_mod_cast h
  obtain ⟨x, y, -, hsA⟩ := Finset.card_eq_two.mp (hsAcard.trans hsf)
  have hspan : Ideal.span ({x, y} : Set R) = IsLocalRing.maximalIdeal R := by
    rw [← hsAspan, hsA]
    simp
  refine ⟨x, y, hspan,
    ((IsRegularLocalRing.isRegular_and_isRegularLocalRing_quotient_and_isMaximalCohenMacaulay
      R).1 [x, y] ?_ (by simp [hsf])).1⟩
  rw [← hspan, Ideal.ofList_cons, Ideal.ofList_cons, Ideal.ofList_nil]
  simp [Ideal.span_insert]

/-- **Blowing up a regular two-dimensional closed point keeps `H¹(𝒪) = 0`.** Let `W` be a locally
Noetherian scheme with `H¹(W, 𝒪_W) = 0` and `w ∈ W` a closed point whose local ring is regular of
dimension two. Then the blowup `W'` of `W` at `w` has `H¹(W', 𝒪_{W'}) = 0`.

The maximal ideal of `𝒪_{W, w}` is generated by a regular sequence of length two, which spreads
out to two generators of the ideal of `w` over an affine neighbourhood `V`; the part of `W'` over
`V` then has `H¹ = 0` (`subsingleton_cohomologyPresheaf_one_preimage_blowUp`), and the blowup is
an isomorphism over `W ∖ {w}`, so
`subsingleton_cohomologyPresheaf_one_top_of_isIso_morphismRestrict` applies. -/
theorem isZeroFirstStructureSheafCohomology_blowUp_of_isRegularLocalRing {W : Scheme.{u}}
    [IsLocallyNoetherian W] (w : W) (hw : IsClosed ({w} : Set W))
    (hreg : IsRegularLocalRing (W.presheaf.stalk w))
    (hdim : ringKrullDim (W.presheaf.stalk w) = 2)
    (hW : IsZeroFirstStructureSheafCohomology W) :
    IsZeroFirstStructureSheafCohomology
      (blowUp (Scheme.IdealSheafData.vanishingIdeal ⟨{w}, hw⟩)) := by
  set M := Scheme.IdealSheafData.vanishingIdeal (⟨{w}, hw⟩ : Closeds W) with hM
  set R := W.presheaf.stalk w
  classical
  obtain ⟨x, y, hspan, hregxy⟩ := exists_span_pair_eq_maximalIdeal_isRegular R hdim
  have hwM : w ∈ M.support := by
    change w ∈ (M.support : Set W)
    simp [hM]
  have hstalk : Stacks.AlgebraicGeometry.stalkIdeal M w hwM =
      Ideal.span (Set.range ![x, y]) := by
    obtain ⟨V₀, hV₀, hwV₀, -⟩ := Opens.isBasis_iff_nbhd.mp W.isBasis_affineOpens
      (show w ∈ (⊤ : W.Opens) from trivial)
    rw [Stacks.AlgebraicGeometry.stalkIdeal_eq_map_germ M w hwM hV₀ hwV₀,
      ← IdealSheafData.stalk_eq_map_germ M w ⟨V₀, hV₀⟩ hwV₀,
      IdealSheafData.stalk_vanishingIdeal_singleton w hw, ← hspan]
    congr 1
    ext z
    simp [Matrix.range_cons, Matrix.range_empty, Set.union_empty, or_comm]
  obtain ⟨V, hwV, a, ha, -⟩ :=
    Stacks.AlgebraicGeometry.RegularIdealSheaf.exists_affineOpen_span_eq_ideal_isRegular_germ M w
      hwM ![x, y] hstalk (by simpa using hregxy)
  have ha' : M.ideal V = Ideal.span {a 0, a 1} := by
    rw [ha]
    congr 1
    ext z
    simp [Fin.exists_fin_two, eq_comm]
  let U : W.Opens := ⟨M.supportᶜ, M.support.isClosed.isOpen_compl⟩
  have : IsIso (blowUpToBase M ∣_ U) := isIso_blowUp_restrict_compl_support M
  have hUV : V.1 ⊔ U = ⊤ := by
    refine top_le_iff.mp fun z _ => ?_
    by_cases hz : z = w
    · exact Or.inl (hz ▸ hwV)
    · refine Or.inr ?_
      change z ∉ (M.support : Set W)
      simpa [hM] using hz
  have := hasExt_sheaf_opens_ab W
  have := hasExt_sheaf_opens_ab (blowUp M)
  exact (Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top _ 1).2 <|
    subsingleton_cohomologyPresheaf_one_top_of_isIso_morphismRestrict (blowUpToBase M) U V.1
      hUV ((Stacks.Cohomology.TerminalCohomology.subsingleton_H_iff_subsingleton_H'_top _ 1).1 hW)
      (subsingleton_cohomologyPresheaf_one_preimage_blowUp M V (a 0) (a 1) ha')

end AlgebraicGeometry

end
