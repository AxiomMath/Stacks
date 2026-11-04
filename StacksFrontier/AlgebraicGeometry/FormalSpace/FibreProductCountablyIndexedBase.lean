module

public import StacksFrontier.AlgebraicGeometry.FormalSpace.Affine.Factorization
public import StacksFrontier.AlgebraicGeometry.Spaces.QuasiCompactFpqcLocalAtTarget
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountableColimit
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablePresentation
public import StacksFrontier.AlgebraicGeometry.FormalSpace.CountablyIndexed
public import StacksFrontier.CategoryTheory.PullbackCancelMono
public import StacksFrontier.CategoryTheory.Sites.MonoOutOfFilteredColimit

/-!
# Replacing the base of a fibre product by a countably indexed one

Let `S` be a scheme contained in a big fppf site `B`, let `V` be an affine formal algebraic
space over `S` and let `t : U ⟶ V` and `s : W ⟶ V` be morphisms from countably indexed affine
formal algebraic spaces. Then `t` and `s` factor through a *countably indexed* affine formal
algebraic space `V'` by a monomorphism `V' ⟶ V`, and `U ×_{V'} W ≅ U ×_V W`.

This is the first step of the affine case of the proof of **Stacks 0GBB**. The clauses of that
tag are proved by reduction to the fibre product of two affine formal algebraic spaces of the
type in question over an affine formal algebraic space, and that case is settled by the
identification of the fibre product with the formal spectrum of a completed tensor product
(**Stacks 0AN3**, clause (3)) followed by **Stacks 0GB4**. Clause (3) of Stacks 0AN3 needs all
three of its spaces to be McQuillan, and an affine formal algebraic space need not be; what the
source does, and what this file does, is to shrink the base until it is countably indexed, which
by **Stacks 0AIK** makes it McQuillan.

## Main results

* `AlgebraicGeometry.FormalSpace.exists_isCountablyIndexed_base`: the countably indexed base
  `V'`, with the factorisations and the monomorphism to `V`.
* `AlgebraicGeometry.FormalSpace.exists_isCountablyIndexed_base_pullback`: the same together
  with the isomorphism `U ×_{V'} W ≅ U ×_V W`.

## Implementation notes

The base `V` is a directed colimit `colim_λ V_λ` of affine schemes of the site along thickenings
and `U` is such a colimit `colim_n U_n` indexed by `ℕ`. Each `U_n` is quasi-compact, so the
composite `U_n ⟶ U ⟶ V` factors through one stage `V_{λ(n)}` by **Stacks 0AIA**; likewise for
`W`. Directedness of the index then produces a monotone `ν : ℕ → Λ` dominating both families,
and `V'` is the colimit of the subdiagram along `ν`.

Three things make that `V'` do what is wanted. It is a countable colimit of affine schemes of
the site along thickenings, so it is countably indexed and — the set-theoretic condition of
Stacks 0AIS being automatic for a countable colimit,
`AlgebraicGeometry.FormalSpace.satisfiesSetTheoreticCondition_of_countable_colimit` — an affine
formal algebraic space. The comparison morphism `V' ⟶ V` is a monomorphism, which is
`CategoryTheory.Sheaf.mono_colimit_pre_of_mono_transition`. And a monomorphism in the base of a
cartesian square may be cancelled, `CategoryTheory.isPullback_comp_mono`, so the two fibre
products agree.

The factorisations `U ⟶ V'` and `W ⟶ V'` are assembled from the stagewise ones by the universal
property of `colim_n U_n`. Their compatibility over the transition morphisms of that colimit is
not proved directly: the two sides agree after composition with the monomorphism `V' ⟶ V`,
where both are the stagewise restriction of `t`.

## References

* [Stacks Project, Tag 0AIA](https://stacks.math.columbia.edu/tag/0AIA)
* [Stacks Project, Tag 0AIK](https://stacks.math.columbia.edu/tag/0AIK)
* [Stacks Project, Tag 0AIS](https://stacks.math.columbia.edu/tag/0AIS)
* [Stacks Project, Tag 0AN3](https://stacks.math.columbia.edu/tag/0AN3)
* [Stacks Project, Tag 0GB4](https://stacks.math.columbia.edu/tag/0GB4)
* [Stacks Project, Tag 0GBB](https://stacks.math.columbia.edu/tag/0GBB)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits

namespace AlgebraicGeometry.FormalSpace

universe u

/-- Two sequences in a directed preorder are dominated by one monotone sequence. -/
theorem exists_monotone_forall_le {Λ : Type*} [Preorder Λ] [IsDirected Λ (· ≤ ·)]
    (a b : ℕ → Λ) : ∃ ν : ℕ → Λ, Monotone ν ∧ (∀ n, a n ≤ ν n) ∧ ∀ n, b n ≤ ν n := by
  choose sup hsupl hsupr using fun x y : Λ ↦ directed_of (· ≤ ·) x y
  refine ⟨fun n ↦ Nat.rec (sup (a 0) (b 0))
    (fun k prev ↦ sup prev (sup (a (k + 1)) (b (k + 1)))) n, ?_, ?_, ?_⟩
  · exact monotone_nat_of_le_succ fun n ↦ hsupl _ _
  · rintro (_ | k)
    exacts [hsupl _ _, (hsupl _ _).trans (hsupr _ _)]
  · rintro (_ | k)
    exacts [hsupr _ _, (hsupr _ _).trans (hsupr _ _)]

/-- Let `V ≅ colim FV` and `X ≅ colim_n FX` with `n` ranging over `ℕ`. If a morphism `r : X ⟶ V`
restricts on each stage `FX n` to a morphism into a stage `FV (lam n)` with `lam ≤ ν`, and the
comparison `colim (FV ∘ ν) ⟶ colim FV` is a monomorphism, then `r` factors through
`colim (FV ∘ ν)`. -/
private theorem exists_comp_colimit_pre_eq_of_factor {C : Type*} [Category C] {Λ : Type*}
    [Preorder Λ] {ν : ℕ → Λ} (hν : Monotone fun n : ULift.{u + 1} ℕ ↦ ν n.down) {FV : Λ ⥤ C}
    [HasColimit FV] [HasColimit (hν.functor ⋙ FV)] [Mono (colimit.pre FV hν.functor)] {V : C}
    (eV : V ≅ colimit FV) {FX : ℕ ⥤ C} [HasColimit FX] {X : C} (e : X ≅ colimit FX) (r : X ⟶ V)
    {lam : ℕ → Λ} (hlam : ∀ n, lam n ≤ ν n) (g : ∀ n, FX.obj n ⟶ FV.obj (lam n))
    (hg : ∀ n, g n ≫ colimit.ι FV (lam n) ≫ eV.inv = colimit.ι FX n ≫ e.inv ≫ r) :
    ∃ r' : X ⟶ colimit (hν.functor ⋙ FV), r' ≫ colimit.pre FV hν.functor ≫ eV.inv = r := by
  let a : ∀ n : ℕ, FX.obj n ⟶ colimit (hν.functor ⋙ FV) := fun n ↦
    g n ≫ FV.map (homOfLE (hlam n)) ≫ colimit.ι (hν.functor ⋙ FV) (ULift.up n)
  have hai : ∀ n, a n ≫ colimit.pre FV hν.functor ≫ eV.inv = colimit.ι FX n ≫ e.inv ≫ r := by
    intro n
    have h₁ : colimit.ι (hν.functor ⋙ FV) (ULift.up n) ≫ colimit.pre FV hν.functor ≫ eV.inv
        = colimit.ι FV (ν n) ≫ eV.inv := by
      rw [colimit.ι_pre_assoc]
      rfl
    simp only [a, Category.assoc]
    rw [h₁, colimit.w_assoc]
    exact hg n
  have hcoc : ∀ (n m : ℕ) (f : n ⟶ m),
      FX.map f ≫ a m = a n ≫ ((Functor.const ℕ).obj (colimit (hν.functor ⋙ FV))).map f := by
    intro n m f
    simp only [Functor.const_obj_obj, Functor.const_obj_map, Category.comp_id]
    rw [← cancel_mono (colimit.pre FV hν.functor ≫ eV.inv)]
    simp only [Category.assoc]
    rw [hai m, hai n, colimit.w_assoc]
  let c : Cocone FX := { pt := _, ι := { app := a, naturality := fun {n m} f ↦ hcoc n m f } }
  have hd : colimit.desc FX c ≫ colimit.pre FV hν.functor ≫ eV.inv = e.inv ≫ r :=
    colimit.hom_ext fun n ↦ by rw [colimit.ι_desc_assoc]; exact hai n
  exact ⟨e.hom ≫ colimit.desc FX c, by rw [Category.assoc, hd, Iso.hom_inv_id_assoc]⟩

variable (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- The transition morphisms of an affine presentation along thickenings are monomorphisms of
fppf sheaves: a thickening of schemes is a closed immersion, hence a monomorphism of schemes,
hence a monomorphism of objects of the site, and the sheafified Yoneda embedding carries a
monomorphism with monomorphic underlying morphism of schemes to a monomorphism. -/
theorem mono_sheafifiedYoneda_map_presentation {Λ : Type*} [Category Λ]
    (D : Λ ⥤ BigAffineFppf B S hS)
    (hD : ∀ ⦃i j : Λ⦄ (f : i ⟶ j),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (D.map f)))
    {a b : Λ} (f : a ⟶ b) :
    Mono ((D ⋙ BigAffineFppf.inclusion B S hS ⋙
      Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)).map f) := by
  have : IsClosedImmersion ((BigFppfOver.toScheme B S hS).map
      ((BigAffineFppf.inclusion B S hS).map (D.map f))) := (hD f).1
  exact Sheaf.mono_sheafifiedYoneda_map_of_mono_underlying (BigFppfOver.topology B S hS)
    (BigFppfOver.toScheme B S hS) ((BigAffineFppf.inclusion B S hS).map (D.map f)) inferInstance

/-- **The base of a fibre product of countably indexed affine formal algebraic spaces may be
shrunk to a countably indexed one.** Let `V` be an affine formal algebraic space over `S` and
let `t : U ⟶ V` and `s : W ⟶ V` be morphisms from countably indexed fppf sheaves. Then `t` and
`s` factor through a countably indexed affine formal algebraic space `V'` mapping to `V` by a
monomorphism.

This is the step of the proof of **Stacks 0GBB** which makes the base McQuillan: by
**Stacks 0AIK** a countably indexed affine formal algebraic space is McQuillan, whereas an
arbitrary one need not be, and clause (3) of **Stacks 0AN3** — the identification of the fibre
product with the formal spectrum of a completed tensor product — asks all three of its spaces
to be McQuillan. -/
theorem exists_isCountablyIndexed_base {U V W : FppfSheaf B S hS} (t : U ⟶ V) (s : W ⟶ V)
    (hU : IsCountablyIndexed B S hS U) (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (hW : IsCountablyIndexed B S hS W) :
    ∃ (V' : FppfSheaf B S hS) (i : V' ⟶ V) (t' : U ⟶ V') (s' : W ⟶ V'),
      IsAffineFormalAlgebraicSpace B S hS V' ∧ IsCountablyIndexed B S hS V' ∧
        Mono i ∧ t' ≫ i = t ∧ s' ≫ i = s := by
  classical
  obtain ⟨DU, hDU, ⟨eU⟩⟩ := id hU
  obtain ⟨DW, hDW, ⟨eW⟩⟩ := id hW
  obtain ⟨-, Λ, pre, hΛne, hΛdir, DV, hDV, ⟨eV⟩⟩ := id hV
  let : Preorder Λ := pre
  let : Nonempty Λ := hΛne
  let : IsDirected Λ (· ≤ ·) := hΛdir
  let Gy := Sheaf.sheafifiedYoneda (BigFppfOver.topology B S hS)
  let FV := DV ⋙ BigAffineFppf.inclusion B S hS ⋙ Gy
  -- Stacks 0AIA: a stage of a sequential presentation maps into a single stage of `V`
  have hfac : ∀ (D : ℕ ⥤ BigAffineFppf B S hS) (X : FppfSheaf B S hS)
      (e : X ≅ colimit (D ⋙ BigAffineFppf.inclusion B S hS ⋙ Gy)) (r : X ⟶ V) (n : ℕ),
      ∃ (lam : Λ) (g : Gy.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj n)) ⟶ FV.obj lam),
        g ≫ colimit.ι FV lam ≫ eV.inv =
          colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ Gy) n ≫ e.inv ≫ r := fun D X e r n ↦
    exists_factor_through_thickening' B S hS Λ DV (fun _ _ g ↦ (hDV g).1) V eV
      (yoneda.obj ((BigAffineFppf.inclusion B S hS).obj (D.obj n)))
      (AlgebraicGeometry.Space.isQuasiCompactSpace_yoneda_of_isAffine B S hS _
        (BigAffineFppf.isAffine_toScheme_obj B S hS (D.obj n)))
      (colimit.ι (D ⋙ BigAffineFppf.inclusion B S hS ⋙ Gy) n ≫ e.inv ≫ r)
  choose lamU gU hgU using fun n ↦ hfac DU U eU t n
  choose lamW gW hgW using fun n ↦ hfac DW W eW s n
  obtain ⟨ν, hνmono, hνU, hνW⟩ := exists_monotone_forall_le lamU lamW
  have hν : Monotone fun n : ULift.{u + 1, 0} ℕ ↦ ν n.down := fun _ _ h ↦ hνmono h
  let DV' := hν.functor ⋙ DV
  have hDV' : ∀ ⦃a b : ULift.{u + 1, 0} ℕ⦄ (f : a ⟶ b),
      Stacks.Thickenings.IsThickening ((BigAffineFppf.toScheme B S hS).map (DV'.map f)) :=
    fun {_ _} f ↦ hDV (hν.functor.map f)
  have : Mono (colimit.pre FV hν.functor) := Sheaf.mono_colimit_pre_of_mono_transition FV
    (fun _ _ f ↦ mono_sheafifiedYoneda_map_presentation B S hS DV hDV f) hν.functor
  obtain ⟨t', ht'⟩ := exists_comp_colimit_pre_eq_of_factor hν eV eU t hνU gU hgU
  obtain ⟨s', hs'⟩ := exists_comp_colimit_pre_eq_of_factor hν eV eW s hνW gW hgW
  refine ⟨_, colimit.pre FV hν.functor ≫ eV.inv, t', s',
    ⟨satisfiesSetTheoreticCondition_of_countable_colimit B S hS DV' hDV' _ ⟨Iso.refl _⟩,
      ULift.{u + 1, 0} ℕ, inferInstance, inferInstance, inferInstance, DV',
      hDV', ⟨Iso.refl _⟩⟩,
    (isCountablyIndexed_iff_exists_countable_presentation B S hS _).2
      ⟨ULift.{u + 1, 0} ℕ, inferInstance, inferInstance, inferInstance, inferInstance, DV',
        hDV', ⟨Iso.refl _⟩⟩,
    inferInstance, ht', hs'⟩

/-- **The fibre product of two countably indexed fppf sheaves over an affine formal algebraic
space is a fibre product over a countably indexed affine formal algebraic space.** The base is
shrunk by `AlgebraicGeometry.FormalSpace.exists_isCountablyIndexed_base`, and a monomorphism in
the base of a cartesian square may be cancelled, so the fibre product is unchanged. -/
theorem exists_isCountablyIndexed_base_pullback {U V W : FppfSheaf B S hS} (t : U ⟶ V)
    (s : W ⟶ V) (hU : IsCountablyIndexed B S hS U) (hV : IsAffineFormalAlgebraicSpace B S hS V)
    (hW : IsCountablyIndexed B S hS W) :
    ∃ (V' : FppfSheaf B S hS) (t' : U ⟶ V') (s' : W ⟶ V'),
      IsAffineFormalAlgebraicSpace B S hS V' ∧ IsCountablyIndexed B S hS V' ∧
        Nonempty (pullback t' s' ≅ pullback t s) := by
  obtain ⟨V', i, t', s', hV'aff, hV'c, _, rfl, rfl⟩ :=
    exists_isCountablyIndexed_base B S hS t s hU hV hW
  exact ⟨V', t', s', hV'aff, hV'c,
    ⟨(isPullback_comp_mono (IsPullback.of_hasPullback t' s') i).isoPullback⟩⟩

end AlgebraicGeometry.FormalSpace

end
