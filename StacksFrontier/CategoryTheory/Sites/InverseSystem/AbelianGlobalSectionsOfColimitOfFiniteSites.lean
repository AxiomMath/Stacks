module

public import StacksFrontier.CategoryTheory.Sites.InverseSystem.GlobalSectionsOfColimitOfFiniteSites

/-! # Global sections of a colimit of abelian sheaves on a colimit of sites (09YP, degree zero)

`Stacks.WeakSites.ColimitGlobalSections.globalSections_colimit_pullback_of_colimit` computes the
global sections — the sections over the **terminal sheaf** — of `G = colim f_i^{-1}F_i` on a
colimit of sites, for a system of sheaves of **sets**, from a finite one-hypercover of the
terminal sheaf at one level. Stacks 09YP is about *abelian* sheaves, and this file carries that
statement over to them, in degree zero: the global sections `Γ(C, 𝒢)` of Mathlib's
`CategoryTheory.Sheaf.Γ` are the filtered colimit of the `Γ(C_n, F_n)`.

The passage is **not** the forgetful image of an abelian colimit presentation. The forgetful
functor `Sheaf K Ab ⥤ Sheaf K (Type _)` is a right adjoint, so it has no reason to preserve the
colimit `colim f_i^{-1}F_i`, and the universal property of
`Stacks.WeakSites.ColimitSiteCohomology.IsColimitPresentation` quantifies only over abelian
sheaves: a compatible family of maps of *sheaves of sets* out of the system has no reason to
factor through `𝒢`. Nothing here asks it to. What is used instead is that the *object-level*
conclusion of Stacks 09YN for an abelian system — joint surjectivity of the legs over an object of
the colimit site, and separatedness — is already an element-level statement about the very same
sets, namely
`Stacks.WeakSites.ColimitSiteCohomology.abelianSections_jointlySurjective_and_separated`. Those two
clauses are exactly the hypotheses `hsurj` and `hsep` of the degree-zero Cech step, and the
underlying presheaf of sets of an abelian sheaf is a sheaf of sets (`sheafCompose`), so the step
applies to the underlying data verbatim. Sheafification never enters.

## Main definitions

* `abGammaEquivSections` — **the global sections of an abelian sheaf are the compatible families
  of sections of its underlying presheaf**, by the restriction maps `CategoryTheory.Sheaf.ΓRes`.
  Global sections are a limit over the site (`CategoryTheory.Sheaf.isLimitConeΓ`) and `forget Ab`
  preserves limits, so this is `CategoryTheory.Limits.Types.isLimitEquivSections`. It is the
  abelian analogue of Mathlib's `CategoryTheory.Sheaf.ΓObjEquivSections`, which is stated only for
  sheaves of sets.
* `forgetSheaf` — the underlying sheaf of sets of an abelian sheaf.

## Main results

* `abelianGlobalSections_colimit_pullback_of_colimit` — **Stacks 09YP over the terminal sheaf, in
  degree zero, for abelian sheaves.** Given an abelian colimit presentation on a colimit of sites
  and a finite one-hypercover of the terminal sheaf at a level `i₀` whose transition images and
  whose image in the colimit site are again such, the global sections of `𝒢` are the filtered
  colimit of the global sections of the `F_n` over the arrows `n ⟶ i₀`.
* `abGamma_eq_of_eq_on_topOneHypercover` and `existsUnique_abGamma_of_matching` — **the sheaf
  condition over the terminal sheaf, for `CategoryTheory.Sheaf.Γ` of an abelian sheaf.** A global
  section is determined by its restrictions to the objects of a one-hypercover of the terminal
  sheaf, and a matching family over those objects glues to a unique global section; these are
  the abelian forms of `sections_eq_of_eq_on_topOneHypercover` and
  `existsUnique_sections_of_matching`. The first is the separatedness input that upgrades the
  second clause of `abelianGlobalSections_colimit_pullback_of_colimit` — agreement after
  restriction to the `W k` at a further level — to equality of global sections there, which is
  what a colimit of abelian groups needs.

## Implementation notes

The map `ρ` on global sections is quantified over and pinned by `hρ` through the restriction maps
`CategoryTheory.Sheaf.ΓRes`, exactly as in the set-valued statement and for the same reason: a
global section is determined by its restrictions rather than given by a formula, so there is no
closed form for `ρ` to be equated with.

The element-form of the abelian compatibility conditions — the composition law of the transitions
and the compatibility of the legs — is
`Stacks.WeakSites.ColimitSiteCohomology.transition_comp_apply` and
`Stacks.WeakSites.ColimitSiteCohomology.IsCompatible.app_apply`; both are stated there because the
`eqToHom` bookkeeping they do is about the system and not about sheaves of sets.

## References

* [Stacks 09YP](https://stacks.math.columbia.edu/tag/09YP)
* [Stacks 09YQ](https://stacks.math.columbia.edu/tag/09YQ)
* [Stacks 09YN](https://stacks.math.columbia.edu/tag/09YN)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite
open CategoryTheory.Sites.InverseSystem
open Stacks.WeakSites.ColimitSiteCohomology

universe u₁ u₂ w

namespace Stacks.WeakSites.ColimitGlobalSections

/-! ### Global sections of an abelian sheaf as compatible families -/

section AbelianGamma

variable {A : Type w} [SmallCategory A] (JA : GrothendieckTopology A)
  [HasWeakSheafify JA Ab.{w}]

/-- The underlying sheaf of sets of an abelian sheaf. -/
abbrev forgetSheaf (𝒢 : Sheaf JA Ab.{w}) : Sheaf JA (Type w) :=
  (sheafCompose JA (forget Ab.{w})).obj 𝒢

/-- **The global sections of an abelian sheaf are the compatible families of sections of its
underlying presheaf**, the equivalence being given by the restriction maps
`CategoryTheory.Sheaf.ΓRes`.

Global sections are a limit over the site (`CategoryTheory.Sheaf.isLimitConeΓ`) and `forget Ab`
preserves limits, so the image of that limit cone under `forget Ab` is a limit cone of the
underlying presheaf of sets, whose cone point is its set of sections
(`CategoryTheory.Limits.Types.isLimitEquivSections`).

This is the abelian analogue of Mathlib's `CategoryTheory.Sheaf.ΓObjEquivSections`, which is
stated only for sheaves of sets. -/
def abGammaEquivSections (𝒢 : Sheaf JA Ab.{w}) :
    ((Sheaf.Γ JA Ab.{w}).obj 𝒢 : Type w) ≃ (𝒢.obj ⋙ forget Ab.{w}).sections :=
  Types.isLimitEquivSections (isLimitOfPreserves (forget Ab.{w}) 𝒢.isLimitConeΓ)

/-- The value at `U` of the compatible family attached to a global section is its restriction
to `U`. -/
lemma abGammaEquivSections_val (𝒢 : Sheaf JA Ab.{w}) (s : (Sheaf.Γ JA Ab.{w}).obj 𝒢) (U : Aᵒᵖ) :
    (abGammaEquivSections JA 𝒢 s).val U = Sheaf.ΓRes 𝒢 U s := rfl

/-- Restricting the global section attached to a compatible family recovers the family. -/
private lemma ΓRes_abGammaEquivSections_symm (𝒢 : Sheaf JA Ab.{w})
    (t : (𝒢.obj ⋙ forget Ab.{w}).sections) (U : Aᵒᵖ) :
    Sheaf.ΓRes 𝒢 U ((abGammaEquivSections JA 𝒢).symm t) = t.val U := by
  rw [← abGammaEquivSections_val, Equiv.apply_symm_apply]

section TopOneHypercover

variable {κ ν : Type*} {W : κ → A} {P : κ → κ → ν → A}
  {p₁ : ∀ k l m, P k l m ⟶ W k} {p₂ : ∀ k l m, P k l m ⟶ W l}

/-- **A global section of an abelian sheaf is determined by its restrictions to the objects of a
one-hypercover of the terminal sheaf.** This is `sections_eq_of_eq_on_topOneHypercover` for the
global sections of `CategoryTheory.Sheaf.Γ` rather than for the sections of a presheaf of sets,
read through `abGammaEquivSections`; only the `coversTop` half of the hypercover is used.

It is the separatedness input that turns the second clause of
`abelianGlobalSections_colimit_pullback_of_colimit` — agreement after restriction to the `W k` at
a further level — into equality of global sections at that level. -/
theorem abGamma_eq_of_eq_on_topOneHypercover (h : IsTopOneHypercover JA W P p₁ p₂)
    (𝒢 : Sheaf JA Ab.{w}) {s s' : (Sheaf.Γ JA Ab.{w}).obj 𝒢}
    (hss : ∀ k, Sheaf.ΓRes 𝒢 (op (W k)) s = Sheaf.ΓRes 𝒢 (op (W k)) s') : s = s' :=
  (abGammaEquivSections JA 𝒢).injective
    (sections_eq_of_eq_on_topOneHypercover h (forgetSheaf JA 𝒢).cond fun k => by
      rw [abGammaEquivSections_val, abGammaEquivSections_val]
      exact hss k)

/-- **The sheaf condition over the terminal sheaf, for the global sections of an abelian sheaf.**
A family of sections of `𝒢` over the objects `W k` of a one-hypercover of the terminal sheaf which
matches on the `P k l m` is the restriction of a unique global section, in the sense of
`CategoryTheory.Sheaf.Γ`.

This is `existsUnique_sections_of_matching` read through `abGammaEquivSections`. -/
theorem existsUnique_abGamma_of_matching (h : IsTopOneHypercover JA W P p₁ p₂)
    (𝒢 : Sheaf JA Ab.{w}) (x : ∀ k, (𝒢.obj ⋙ forget Ab.{w}).obj (op (W k)))
    (hx : ∀ k l m, (𝒢.obj ⋙ forget Ab.{w}).map (p₁ k l m).op (x k) =
      (𝒢.obj ⋙ forget Ab.{w}).map (p₂ k l m).op (x l)) :
    ∃! s : (Sheaf.Γ JA Ab.{w}).obj 𝒢, ∀ k, Sheaf.ΓRes 𝒢 (op (W k)) s = x k := by
  obtain ⟨t, ht, -⟩ := existsUnique_sections_of_matching h (forgetSheaf JA 𝒢).cond x hx
  have key := fun k => ΓRes_abGammaEquivSections_symm JA 𝒢 t (op (W k))
  exact ⟨(abGammaEquivSections JA 𝒢).symm t, fun k => (key k).trans (ht k),
    fun s hs => abGamma_eq_of_eq_on_topOneHypercover JA h 𝒢
      fun k => (hs k).trans ((key k).trans (ht k)).symm⟩

end TopOneHypercover

end AbelianGamma

/-! ### The degree-zero colimit statement for abelian global sections -/

section AbelianMain

variable (D : InverseSystemOfFiniteSites.{u₁, u₂, max u₁ u₂ w}) {C : Type (max u₁ u₂ w)}
  [SmallCategory C]
  (uC : ∀ i, D.C i ⥤ C)
  (hu : ∀ {i j : D.I} (a : i ⟶ j), D.u a ⋙ uC i = uC j)
  (hobj : ∀ Y : C, ∃ (i : D.I) (Z : D.C i), (uC i).obj Z = Y)
  (hhom : ∀ (i : D.I) (Y Z : D.C i) (f : (uC i).obj Y ⟶ (uC i).obj Z),
    ∃ (j : D.I) (a : j ⟶ i) (g : (D.u a).obj Y ⟶ (D.u a).obj Z),
      (uC j).map g =
        eqToHom (Functor.congr_obj (hu a) Y) ≫ f ≫ eqToHom (Functor.congr_obj (hu a) Z).symm)
  (hhom_inj : ∀ (i : D.I) (Y Z : D.C i) (g₁ g₂ : Y ⟶ Z),
    (uC i).map g₁ = (uC i).map g₂ →
      ∃ (j : D.I) (a : j ⟶ i), (D.u a).map g₁ = (D.u a).map g₂)
  (K : Precoverage C)
  (hK : ∀ (Y : C) (R : Presieve Y), R ∈ K Y ↔
    ∃ (i : D.I) (Z : D.C i) (h : (uC i).obj Z = Y) (S : Presieve Z),
      S ∈ (D.J i).toPrecoverage Z ∧ S ∈ Precoverage.finite (D.C i) Z ∧
        R = h ▸ S.map (uC i))
  (F : InverseSystemOfFiniteSites.AbelianSheafSystem.{u₁, u₂, max u₁ u₂ w, max u₁ u₂ w} D)
  (𝒢 : Sheaf K.toGrothendieck Ab.{max u₁ u₂ w})
  (ι : ∀ j, (F.obj j).obj ⟶ (uC j).op ⋙ 𝒢.obj)
  (hcolim : IsColimitPresentation.{u₁, u₂, max u₁ u₂ w, max u₁ u₂ w} D uC hu K F 𝒢 ι)
  {κ' ν' : Type} [Finite κ'] [Finite ν'] (i₀ : D.I) (W₀ : κ' → D.C i₀)
  (P₀ : κ' → κ' → ν' → D.C i₀)
  (q₁ : ∀ k l m, P₀ k l m ⟶ W₀ k) (q₂ : ∀ k l m, P₀ k l m ⟶ W₀ l)
  (hlev : ∀ {n : D.I} (a : n ⟶ i₀), IsTopOneHypercover (D.J n)
    (fun k => (D.u a).obj (W₀ k)) (fun k l m => (D.u a).obj (P₀ k l m))
    (fun k l m => (D.u a).map (q₁ k l m)) (fun k l m => (D.u a).map (q₂ k l m)))
  (hC : IsTopOneHypercover K.toGrothendieck (fun k => (uC i₀).obj (W₀ k))
    (fun k l m => (uC i₀).obj (P₀ k l m)) (fun k l m => (uC i₀).map (q₁ k l m))
    (fun k l m => (uC i₀).map (q₂ k l m)))
  (ρ : ∀ {n : D.I} (_ : n ⟶ i₀),
    ((Sheaf.Γ (D.J n) Ab.{max u₁ u₂ w}).obj (F.obj n) : Type (max u₁ u₂ w)) →
      ((Sheaf.Γ K.toGrothendieck Ab.{max u₁ u₂ w}).obj 𝒢 : Type (max u₁ u₂ w)))
  (hρ : ∀ {n : D.I} (a : n ⟶ i₀)
      (t : (Sheaf.Γ (D.J n) Ab.{max u₁ u₂ w}).obj (F.obj n)) (Y : D.C n),
    Sheaf.ΓRes 𝒢 (op ((uC n).obj Y)) (ρ a t) =
      (ι n).app (op Y) (Sheaf.ΓRes (F.obj n) (op Y) t))

include hu hobj hhom hhom_inj hK hcolim hlev hC hρ in
/-- **Stacks 09YP over the terminal sheaf, in degree zero, for abelian sheaves.** Let the functors
`uC i` exhibit `C` as the colimit of the sites of an inverse system of sites with finite coverings,
let `F` be a system of abelian sheaves on the levels with transitions
`Stacks.WeakSites.ColimitSiteCohomology.transition`, and let `𝒢` with legs `ι` present the colimit
`colim f_i^{-1}F_i` (`IsColimitPresentation`). Assume a level `i₀` carries a finite one-hypercover
of the terminal sheaf whose transition images (`hlev`) and whose image in the colimit site (`hC`)
are again such. Then the **global sections** of `𝒢`, in the sense of Mathlib's
`CategoryTheory.Sheaf.Γ`, are the filtered colimit of the global sections of the `F_n` over the
arrows `n ⟶ i₀`: the maps `ρ` are jointly surjective, and two global sections of a level with the
same image agree on the one-hypercover after passing to a further level.

The two object-level inputs are discharged, not assumed: they are the two clauses of
`Stacks.WeakSites.ColimitSiteCohomology.abelianSections_jointlySurjective_and_separated`, which is
Stacks 09YN for an abelian system read on elements. Sheafification plays no part; see the module
documentation for why the forgetful image of an abelian colimit presentation is neither needed nor
available. -/
theorem abelianGlobalSections_colimit_pullback_of_colimit :
    (∀ s : (Sheaf.Γ K.toGrothendieck Ab.{max u₁ u₂ w}).obj 𝒢,
        ∃ (n : D.I) (a : n ⟶ i₀)
          (t : (Sheaf.Γ (D.J n) Ab.{max u₁ u₂ w}).obj (F.obj n)), ρ a t = s) ∧
      ∀ (n : D.I) (a : n ⟶ i₀)
          (t t' : (Sheaf.Γ (D.J n) Ab.{max u₁ u₂ w}).obj (F.obj n)),
        ρ a t = ρ a t' →
          ∃ (m : D.I) (b : m ⟶ n), ∀ k : κ',
            (transition D F b).app (op ((D.u a).obj (W₀ k)))
                (Sheaf.ΓRes (F.obj n) (op ((D.u a).obj (W₀ k))) t) =
              (transition D F b).app (op ((D.u a).obj (W₀ k)))
                (Sheaf.ΓRes (F.obj n) (op ((D.u a).obj (W₀ k))) t') := by
  classical
  obtain ⟨hsurjAb, hsepAb⟩ :=
    abelianSections_jointlySurjective_and_separated D uC hu hobj hhom hhom_inj K hK F 𝒢 ι hcolim
  have hψ : ∀ {i j k : D.I} (a : j ⟶ i) (b : k ⟶ j) (V : D.C i)
      (x : (forgetSheaf (D.J i) (F.obj i)).obj.obj (op V)),
      (Functor.whiskerRight (transition D F (b ≫ a)) (forget Ab.{max u₁ u₂ w})).app (op V) x =
        (forgetSheaf (D.J k) (F.obj k)).obj.map
            (eqToHom (congrArg op (Functor.congr_obj (D.comp b a) V).symm))
          ((Functor.whiskerRight (transition D F b)
              (forget Ab.{max u₁ u₂ w})).app (op ((D.u a).obj V))
            ((Functor.whiskerRight (transition D F a)
              (forget Ab.{max u₁ u₂ w})).app (op V) x)) :=
    fun a b V x => transition_comp_apply D F a b V x
  have hι : ∀ {i j : D.I} (a : j ⟶ i) (V : D.C i)
      (x : (forgetSheaf (D.J i) (F.obj i)).obj.obj (op V)),
      (Functor.whiskerRight (ι i) (forget Ab.{max u₁ u₂ w})).app (op V) x =
        (forgetSheaf K.toGrothendieck 𝒢).obj.map
            (eqToHom (congrArg op (Functor.congr_obj (hu a) V)))
          ((Functor.whiskerRight (ι j) (forget Ab.{max u₁ u₂ w})).app (op ((D.u a).obj V))
            ((Functor.whiskerRight (transition D F a)
              (forget Ab.{max u₁ u₂ w})).app (op V) x)) :=
    fun a V x => IsCompatible.app_apply D uC hu F 𝒢.obj hcolim.1 a V x
  have hsurj : ∀ (i : D.I) (X : D.C i) (s : (forgetSheaf K.toGrothendieck 𝒢).obj.sections),
      ∃ (j : D.I) (a : j ⟶ i)
        (t : (forgetSheaf (D.J j) (F.obj j)).obj.obj (op ((D.u a).obj X))),
        (Functor.whiskerRight (ι j) (forget Ab.{max u₁ u₂ w})).app (op ((D.u a).obj X)) t =
          s.val (op ((uC j).obj ((D.u a).obj X))) := by
    intro i X s
    obtain ⟨j, a, t, ht⟩ := hsurjAb i X (s.val (op ((uC i).obj X)))
    refine ⟨j, a, t, (CategoryTheory.Iso.toEquiv (asIso
      ((forgetSheaf K.toGrothendieck 𝒢).obj.map
        (eqToHom (congrArg op (Functor.congr_obj (hu a) X)))))).injective ?_⟩
    exact ht.trans (s.2 (eqToHom (congrArg op (Functor.congr_obj (hu a) X)))).symm
  have hsep : ∀ (i : D.I) (X : D.C i) (j : D.I) (a : j ⟶ i)
      (t t' : (forgetSheaf (D.J j) (F.obj j)).obj.obj (op ((D.u a).obj X))),
      (Functor.whiskerRight (ι j) (forget Ab.{max u₁ u₂ w})).app (op ((D.u a).obj X)) t =
          (Functor.whiskerRight (ι j) (forget Ab.{max u₁ u₂ w})).app (op ((D.u a).obj X)) t' →
        ∃ (k : D.I) (b : k ⟶ j),
          (Functor.whiskerRight (transition D F b)
              (forget Ab.{max u₁ u₂ w})).app (op ((D.u a).obj X)) t =
            (Functor.whiskerRight (transition D F b)
              (forget Ab.{max u₁ u₂ w})).app (op ((D.u a).obj X)) t' :=
    fun i X j a t t' h => hsepAb i X j a t t' h
  have hρ' : ∀ {n : D.I} (a : n ⟶ i₀) (t : (forgetSheaf (D.J n) (F.obj n)).obj.sections)
      (Y : D.C n),
      (abGammaEquivSections K.toGrothendieck 𝒢
          (ρ a ((abGammaEquivSections (D.J n) (F.obj n)).symm t))).val (op ((uC n).obj Y)) =
        (Functor.whiskerRight (ι n) (forget Ab.{max u₁ u₂ w})).app (op Y) (t.val (op Y)) := by
    intro n a t Y
    rw [abGammaEquivSections_val, hρ a _ Y,
      ΓRes_abGammaEquivSections_symm (D.J n) (F.obj n) t (op Y)]
    rfl
  obtain ⟨hs1, hs2⟩ := globalSections_colimit_pullback_of_colimit D uC hu
    (fun n => forgetSheaf (D.J n) (F.obj n))
    (fun {_ _} a => Functor.whiskerRight (transition D F a) (forget Ab.{max u₁ u₂ w}))
    (forgetSheaf K.toGrothendieck 𝒢)
    (fun n => Functor.whiskerRight (ι n) (forget Ab.{max u₁ u₂ w}))
    hψ hι hsurj hsep i₀ W₀ P₀ q₁ q₂ hlev hC
    (fun {n} a t => abGammaEquivSections K.toGrothendieck 𝒢
      (ρ a ((abGammaEquivSections (D.J n) (F.obj n)).symm t)))
    hρ'
  refine ⟨fun s => ?_, fun n a t t' htt => ?_⟩
  · obtain ⟨n, a, t, ht⟩ := hs1 (abGammaEquivSections K.toGrothendieck 𝒢 s)
    exact ⟨n, a, (abGammaEquivSections (D.J n) (F.obj n)).symm t,
      (abGammaEquivSections K.toGrothendieck 𝒢).injective ht⟩
  · refine hs2 n a (abGammaEquivSections (D.J n) (F.obj n) t)
      (abGammaEquivSections (D.J n) (F.obj n) t') ?_
    simp only [Equiv.symm_apply_apply]
    exact congrArg (abGammaEquivSections K.toGrothendieck 𝒢) htt

end AbelianMain

end Stacks.WeakSites.ColimitGlobalSections

end
