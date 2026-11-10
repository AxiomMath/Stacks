module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DenseSpanGenerators
public import StacksFrontier.AlgebraicGeometry.Size.Cutoff
public import StacksFrontier.AlgebraicGeometry.Size.FiniteType
public import StacksFrontier.AlgebraicGeometry.Size.FiniteTypeCount
public import StacksFrontier.AlgebraicGeometry.Spaces.AffineAtlas
public import StacksFrontier.AlgebraicGeometry.Spaces.InvariantSubspace

/-!
# The points of an algebraic space with values in a one-point affine scheme are few

Let `Y` be an algebraic space over a scheme `S` of a big fppf site, with an étale surjective
atlas `a : h_{U'} ⟶ Y`, and let `U` be an object of the site whose underlying scheme is affine
with exactly one point (for instance the spectrum of a field).  Every `y ∈ Y(U)` lifts to the
atlas after restriction to an affine scheme `W` étale over `U` landing in an affine open of `U'`,
and `W ⟶ U` is an fppf covering, so `y` is determined by the isomorphism class of `W` over `U`,
the affine open of `U'` and a morphism of affine schemes into it.  Counting these data bounds
`#Y(U)` by `2 ^ max (size U) (size U')`.

## Main results

* `AlgebraicGeometry.Scheme.mk_hom_le_of_isAffine`: morphisms into an affine scheme are bounded
  by the maps of global sections.
* `AlgebraicGeometry.Space.mk_obj_le_of_atlas`: the bound on `#Y(U)`.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite Cardinal

universe u

namespace AlgebraicGeometry

variable {B : BigFppfSite.{u}} {S : Scheme.{u}} {hS : B.Contains S}

/-- **Morphisms into an affine scheme are bounded by the maps of global sections**: a morphism
into an affine scheme is determined by its map on global sections. -/
theorem Scheme.mk_hom_le_of_isAffine (X Y : Scheme.{u}) [IsAffine Y] :
    #(X ⟶ Y) ≤ #Γ(X, ⊤) ^ #Γ(Y, ⊤) := by
  rw [Cardinal.power_def]
  exact Cardinal.mk_le_of_injective (f := fun g : X ⟶ Y => (g.appTop.hom : Γ(Y, ⊤) → Γ(X, ⊤)))
    fun g g' h => ext_of_isAffine (CommRingCat.hom_ext (RingHom.ext (congrFun h)))

namespace Space

open Stacks.SheafOfModules.DenseSpan in
/-- **The points of an algebraic space with values in a one-point affine scheme are few.**  If
`a : h_{U'} ⟶ Y` is an étale surjective atlas of the algebraic space `Y`, and the scheme
underlying `U` is affine with exactly one point, then `#Y(U) ≤ 2 ^ max (size U) (size U')`. -/
theorem mk_obj_le_of_atlas {Y : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (hY : IsAlgebraicSpace B S hS Y)
    {U' : BigFppfOver B S hS} (a : yoneda.obj U' ⟶ Y)
    (ha_surj : (MorphismProperty.inverseImage (@Surjective.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (ha_et : (MorphismProperty.inverseImage (@Etale.{u} : MorphismProperty Scheme.{u})
      (BigFppfOver.toScheme B S hS)).presheaf a)
    (U : BigFppfOver B S hS) [IsAffine ((BigFppfOver.toScheme B S hS).obj U)]
    [Nonempty ((BigFppfOver.toScheme B S hS).obj U)]
    [Subsingleton ((BigFppfOver.toScheme B S hS).obj U)] :
    #(Y.obj (op U)) ≤ 2 ^ max ((BigFppfOver.toScheme B S hS).obj U).size
      ((BigFppfOver.toScheme B S hS).obj U').size := by
  set TU := (BigFppfOver.toScheme B S hS).obj U with hTU
  set TU' := (BigFppfOver.toScheme B S hS).obj U' with hTU'
  obtain ⟨I, V, hI, hV⟩ := exists_index_affineFiniteTypeOver TU
  let Data := Σ (x : I) (O : TU'.affineOpens), ((V x).obj ⟶ O.1.toScheme)
  let W : ∀ x : I, B.Contains (V x).obj → BigFppfOver B S hS := fun x hc =>
    siteObject B S hS hc ((V x).hom ≫ B.inclusion.map U.hom)
  let Good : Y.obj (op U) → Data → Prop := fun y d =>
    ∃ (hc : B.Contains (V d.1).obj) (πt : W d.1 hc ⟶ U) (mt : W d.1 hc ⟶ U'),
      (BigFppfOver.toScheme B S hS).map πt = (V d.1).hom ∧
      (BigFppfOver.toScheme B S hS).map mt = d.2.2 ≫ d.2.1.1.ι ∧
      Etale (V d.1).hom ∧ Surjective (V d.1).hom ∧
      Y.map πt.op y = a.app (op (W d.1 hc)) mt
  have key : ∀ y, ∃ d, Good y d := by
    intro y
    let yt : yoneda.obj U ⟶ Y := yonedaEquiv.symm y
    have hrep := ha_et.rep
    let P := hrep.pullback yt
    let q : P ⟶ U := hrep.snd yt
    let p : P ⟶ U' := hrep.fst' yt
    have hw : yoneda.map p ≫ a = yoneda.map q ≫ yt := by
      rw [Functor.relativelyRepresentable.map_fst']
      exact hrep.w yt
    have hqEt : Etale ((BigFppfOver.toScheme B S hS).map q) :=
      ha_et.property yt (hrep.fst yt) (hrep.snd yt) (hrep.isPullback yt)
    have hqSurj : Surjective ((BigFppfOver.toScheme B S hS).map q) :=
      ha_surj.property yt (hrep.fst yt) (hrep.snd yt) (hrep.isPullback yt)
    obtain ⟨u₀⟩ : Nonempty TU := inferInstance
    obtain ⟨x₀, -⟩ := hqSurj.surj u₀
    obtain ⟨O, hO, hpO, -⟩ := exists_isAffineOpen_mem_and_subset
      (show (BigFppfOver.toScheme B S hS).map p x₀ ∈ (⊤ : TU'.Opens) from trivial)
    obtain ⟨Q, hQ, hxQ, hQO⟩ := exists_isAffineOpen_mem_and_subset
      (x := x₀) (U := (BigFppfOver.toScheme B S hS).map p ⁻¹ᵁ O) hpO
    have : IsAffine Q.toScheme := hQ
    obtain ⟨x, e, he⟩ := hV ⟨Q.toScheme, Q.ι ≫ (BigFppfOver.toScheme B S hS).map q, hQ,
      inferInstance⟩
    have hcQ : B.Contains Q.toScheme := Scheme.size_lt_of_isOpenImmersion Q.ι P.left.property
    have hc : B.Contains (V x).obj :=
      lt_of_le_of_lt (Scheme.size_le_of_mono_quasiCompact e.hom) hcQ
    have hrange : Set.range (e.hom ≫ Q.ι ≫ (BigFppfOver.toScheme B S hS).map p) ⊆
        Set.range O.ι := by
      rw [Scheme.Opens.range_ι]
      rintro _ ⟨z, rfl⟩
      exact hQO (e.hom z).2
    let m : (V x).obj ⟶ O.toScheme := IsOpenImmersion.lift O.ι _ hrange
    have hmfac : m ≫ O.ι = e.hom ≫ Q.ι ≫ (BigFppfOver.toScheme B S hS).map p :=
      IsOpenImmersion.lift_fac _ _ _
    refine ⟨⟨x, ⟨O, (hO : O ∈ TU'.affineOpens)⟩, m⟩, hc, ?_⟩
    obtain ⟨πt, hπt⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (X := W x hc) (Y := U)
      (V x).hom rfl
    have hPq : B.inclusion.map P.hom =
        (BigFppfOver.toScheme B S hS).map q ≫ B.inclusion.map U.hom := by
      change B.inclusion.map P.hom = B.inclusion.map q.left ≫ B.inclusion.map U.hom
      rw [← Functor.map_comp, Over.w q]
    obtain ⟨et, het⟩ := BigFppfOver.exists_hom_of_comp_eq B S hS (X := W x hc) (Y := P)
      (e.hom ≫ Q.ι) (by
        change (e.hom ≫ Q.ι) ≫ B.inclusion.map P.hom = (V x).hom ≫ B.inclusion.map U.hom
        rw [hPq, ← he]
        simp only [Category.assoc])
    have hπ : et ≫ q = πt := (BigFppfOver.toScheme B S hS).map_injective (by
      rw [Functor.map_comp, het, hπt, ← he, Category.assoc])
    refine ⟨πt, et ≫ p, hπt, by rw [Functor.map_comp, het, hmfac, Category.assoc], ?_, ?_, ?_⟩
    · rw [← he]
      infer_instance
    · rw [← he]
      exact ⟨fun u => ⟨e.inv.base ⟨x₀, hxQ⟩, Subsingleton.elim _ _⟩⟩
    · have h := congrArg (fun φ => φ.app (op (W x hc)) et) hw
      change a.app _ (et ≫ p) = yt.app _ (et ≫ q) at h
      change Y.map πt.op y = a.app _ (et ≫ p)
      rw [h, hπ]
      rfl
  choose Φ hΦ using key
  have hinj : Function.Injective Φ := by
    intro y y' hyy
    have h1 := hΦ y
    have h2 := hΦ y'
    rw [hyy] at h1
    obtain ⟨hc, πt, mt, hπ, hm, het, hsurj, hy⟩ := h1
    obtain ⟨hc', πt', mt', hπ', hm', -, -, hy'⟩ := h2
    have hππ : πt = πt' := (BigFppfOver.toScheme B S hS).map_injective (hπ.trans hπ'.symm)
    have hmm : mt = mt' := (BigFppfOver.toScheme B S hS).map_injective (hm.trans hm'.symm)
    have hsep : Y.map πt.op y = Y.map πt.op y' := by
      rw [hy, hmm, ← hy', ← hππ]
    have hsurj' : Surjective ((BigFppfOver.toScheme B S hS).map πt) := hπ ▸ hsurj
    have het' : Etale ((BigFppfOver.toScheme B S hS).map πt) := hπ ▸ het
    have hcov := sieve_generate_singleton_mem_topology_over B S hS πt hsurj' het'
    have hsh : Presieve.IsSheaf (BigFppfOver.topology B S hS) Y :=
      (isSheaf_iff_isSheaf_of_type _ _).1 hY.isSheaf
    refine (hsh.isSeparated _ hcov).ext (fun Z f hf => ?_)
    obtain ⟨_, g, k, hk, rfl⟩ := hf
    cases hk
    simp only [op_comp, Functor.map_comp_apply, hsep]
  refine (Cardinal.mk_le_of_injective hinj).trans ?_
  set m := max TU.size TU'.size
  have hm : ℵ₀ ≤ m := TU.aleph0_le_size.trans (le_max_left _ _)
  have h2m : ℵ₀ ≤ 2 ^ m := hm.trans (Cardinal.cantor m).le
  have hmle : m ≤ 2 ^ m := (Cardinal.cantor m).le
  have hΓU : #Γ(TU, ⊤) ≤ TU.size := TU.mk_sections_le_size ⟨⊤, isAffineOpen_top TU⟩
  refine mk_sigma_le_of_le h2m ?_ (fun x => mk_sigma_le_of_le h2m ?_ (fun O => ?_))
  · refine hI.trans ?_
    have : (2 : Cardinal.{u}) ^ max ℵ₀ #Γ(TU, ⊤) ≤ 2 ^ m :=
      Cardinal.power_le_power_left two_ne_zero
        ((max_le TU.aleph0_le_size hΓU).trans (le_max_left _ _))
    exact (mul_le_mul' h2m this).trans (Cardinal.mul_eq_self h2m).le
  · exact (TU'.mk_affineOpens_le_size.trans (le_max_right _ _)).trans hmle
  · have : IsAffine O.1.toScheme := O.2
    refine (Scheme.mk_hom_le_of_isAffine _ _).trans ?_
    have h1 : #Γ((V x).obj, ⊤) ≤ 2 ^ m :=
      (((V x).obj.mk_sections_le_size ⟨⊤, isAffineOpen_top _⟩).trans
        (Scheme.size_le_of_locallyOfFiniteType (V x).hom)).trans ((le_max_left _ _).trans hmle)
    have h2 : #Γ(O.1.toScheme, ⊤) ≤ m := by
      rw [Cardinal.mk_congr (O.1.topIso.commRingCatIsoToRingEquiv.toEquiv)]
      exact (TU'.mk_sections_le_size O).trans (le_max_right _ _)
    calc #Γ((V x).obj, ⊤) ^ #Γ(O.1.toScheme, ⊤) ≤ (2 ^ m) ^ #Γ(O.1.toScheme, ⊤) :=
          Cardinal.power_le_power_right h1
      _ ≤ (2 ^ m) ^ m := Cardinal.power_le_power_left (Cardinal.power_ne_zero _ two_ne_zero) h2
      _ = 2 ^ m := by rw [← Cardinal.power_mul, Cardinal.mul_eq_self hm]

end Space

end AlgebraicGeometry
