module

public import Mathlib.Algebra.Homology.DerivedCategory.KProjective
public import StacksFrontier.Algebra.Module.FinitePresentation.FilteredColimitHom
public import StacksCore.Tactic.StacksAttribute

/-!
# Maps out of a bounded complex of finitely presented modules into a filtered colimit

Let `N` be a system of complexes of `R`-modules over a directed preorder `J` with a compatible
family of maps to `P` which is, in each degree, a filtered colimit of the system. Let `E` be a
complex with only finitely many nonzero terms, each finitely presented. Then
`colim_j Hom_{K(R)}(E, N j) → Hom_{K(R)}(E, P)` is bijective, and the same for `Hom_{D(R)}` when
`E` is in addition a complex of projectives.

## Main results

* `Stacks.FilteredColimitHom.exists_descends_homotopy` and
  `Stacks.FilteredColimitHom.exists_le_eq_of_eq_homotopy`: surjectivity and injectivity of the
  comparison in the homotopy category.
* `Stacks.FilteredColimitHom.exists_descends_derived` and
  `Stacks.FilteredColimitHom.exists_le_eq_of_eq_derived`: the same in the derived category, for
  `E` a bounded complex of projectives.

## Implementation notes

The colimit of hom-groups is not constructed; bijectivity of the comparison out of it is
expressed by its two elementwise clauses, which is what a directed system makes available and
what the consumers use.

Boundedness is taken as a finite set `W` of degrees outside which `E` vanishes, rather than as
`IsStrictlyLE`/`IsStrictlyGE` instances, because the proofs need to range over the nonzero
degrees as a `Finset` in order to take a stage above finitely many stages at once; any bounded
complex supplies such a `W`.

Everything rests on two facts about a single finitely presented module, proved in
`StacksFrontier.Algebra.Module.FinitePresentation.FilteredColimitHom`: a homomorphism into the
colimit factors through a stage, and two homomorphisms into a stage agreeing in the colimit agree
at a later stage. Applying the second to the finitely many commutation identities turns a
degreewise lift into a chain map, and applying it to the finitely many homotopy identities turns a
degreewise lift of a homotopy into a homotopy.

The derived-category statements are obtained from the homotopy-category ones by
`CochainComplex.IsKProjective.Qh_map_bijective`: a complex of projectives that is bounded above
is K-projective, so the localization functor is bijective on maps out of it.

## References

* [Stacks Project, Tag 09RE](https://stacks.math.columbia.edu/tag/09RE)
-/

@[expose] public section

universe u v w

namespace Stacks.FilteredColimitHom

open CategoryTheory CategoryTheory.Limits CochainComplex CochainComplex.HomComplex

/-- The localization of complexes of `R`-modules to the homotopy category. -/
noncomputable abbrev Qh (R : Type u) [Ring R] :
    CochainComplex (ModuleCat.{u} R) ℤ ⥤ HomotopyCategory (ModuleCat.{u} R) (ComplexShape.up ℤ) :=
  HomotopyCategory.quotient (ModuleCat.{u} R) (ComplexShape.up ℤ)

variable {R : Type u} [Ring R] {J : Type v} [Preorder J] [IsDirected J (· ≤ ·)]
  {N : J → CochainComplex (ModuleCat.{u} R) ℤ}
  {t : ∀ ⦃i j : J⦄, i ≤ j → (N i ⟶ N j)}
  {P : CochainComplex (ModuleCat.{u} R) ℤ} {ι : ∀ j, N j ⟶ P}
  {E : CochainComplex (ModuleCat.{u} R) ℤ}

section Degreewise

variable (htrans : ∀ ⦃i j k : J⦄ (h : i ≤ j) (h' : j ≤ k), t h ≫ t h' = t (h.trans h'))
  (hcompat : ∀ ⦃i j : J⦄ (h : i ≤ j), t h ≫ ι j = ι i)
  (hsurj : ∀ (n : ℤ) (x : P.X n), ∃ (j : J) (y : (N j).X n), (ι j).f n y = x)
  (hzero : ∀ (n : ℤ) (j : J) (y : (N j).X n), (ι j).f n y = 0 →
    ∃ (k : J) (h : j ≤ k), (t h).f n y = 0)

include htrans hzero in
/-- Two morphisms out of a finitely presented degree of `E` into a stage which agree in the
colimit agree at a later stage. This is the module-level injectivity, transported to
`ModuleCat`. -/
@[ega "IV 8.5.2.1" "partial, special case"]
theorem exists_le_comp_eq (n m : ℤ) [Module.FinitePresentation R (E.X n)] {j : J}
    (ψ₁ ψ₂ : E.X n ⟶ (N j).X m) (h : ψ₁ ≫ (ι j).f m = ψ₂ ≫ (ι j).f m) :
    ∃ (k : J) (hjk : j ≤ k), ψ₁ ≫ (t hjk).f m = ψ₂ ≫ (t hjk).f m := by
  obtain ⟨k, hjk, hk⟩ := Module.Finite.exists_le_comp_eq_of_comp_eq
    (t := fun _ _ h => ((t h).f m).hom) (ι := fun j => ((ι j).f m).hom)
    (by
      intro i j k h h' x
      have := congrArg
        (fun u : N i ⟶ N k => (ModuleCat.Hom.hom (HomologicalComplex.Hom.f u m)) x) (htrans h h')
      simpa using this)
    (by
      intro j y hy
      obtain ⟨k, hjk, hk⟩ := hzero m j y hy
      exact ⟨k, hjk, hk⟩)
    ψ₁.hom ψ₂.hom (by
      have := congrArg ModuleCat.Hom.hom h
      simpa using this)
  exact ⟨k, hjk, ModuleCat.hom_ext (by simpa using hk)⟩

include htrans hcompat hsurj hzero in
/-- A morphism out of a finitely presented degree of `E` into the colimit factors through some
stage. This is the module-level surjectivity, transported to `ModuleCat`. -/
@[ega "IV 8.5.2.1" "partial"]
theorem exists_lift (n m : ℤ) [Module.FinitePresentation R (E.X n)] (φ : E.X n ⟶ P.X m) :
    ∃ (j : J) (ψ : E.X n ⟶ (N j).X m), ψ ≫ (ι j).f m = φ := by
  obtain ⟨j, ψ, hψ⟩ := Module.FinitePresentation.exists_lift
    (t := fun _ _ h => ((t h).f m).hom) (ι := fun j => ((ι j).f m).hom)
    (by
      intro i j k h h' x
      have := congrArg
        (fun u : N i ⟶ N k => (ModuleCat.Hom.hom (HomologicalComplex.Hom.f u m)) x) (htrans h h')
      simpa using this)
    (by
      intro i j h x
      have := congrArg
        (fun u : N i ⟶ P => (ModuleCat.Hom.hom (HomologicalComplex.Hom.f u m)) x) (hcompat h)
      simpa using this)
    (by
      intro x
      obtain ⟨j, y, hy⟩ := hsurj m x
      exact ⟨j, y, hy⟩)
    (by
      intro j y hy
      obtain ⟨k, hjk, hk⟩ := hzero m j y hy
      exact ⟨k, hjk, hk⟩)
    φ.hom
  exact ⟨j, ModuleCat.ofHom ψ, ModuleCat.hom_ext (by simpa using hψ)⟩

omit [IsDirected J (· ≤ ·)] in
include hcompat in
/-- A transition map followed by the map to the colimit is the map to the colimit, in each
degree. -/
theorem t_comp_ι {i j : J} (h : i ≤ j) (n : ℤ) : (t h).f n ≫ (ι j).f n = (ι i).f n := by
  have := congrArg (fun v : N i ⟶ P => HomologicalComplex.Hom.f v n) (hcompat h)
  simpa using this

omit [IsDirected J (· ≤ ·)] in
include htrans in
/-- Composing two transition maps in a single degree. -/
theorem t_comp_t {i j k : J} (h : i ≤ j) (h' : j ≤ k) (n : ℤ) :
    (t h).f n ≫ (t h').f n = (t (h.trans h')).f n := by
  have := congrArg (fun v : N i ⟶ N k => HomologicalComplex.Hom.f v n) (htrans h h')
  simpa using this

end Degreewise

section Main

variable (htrans : ∀ ⦃i j k : J⦄ (h : i ≤ j) (h' : j ≤ k), t h ≫ t h' = t (h.trans h'))
  (hcompat : ∀ ⦃i j : J⦄ (h : i ≤ j), t h ≫ ι j = ι i)
  (hsurj : ∀ (n : ℤ) (x : P.X n), ∃ (j : J) (y : (N j).X n), (ι j).f n y = x)
  (hzero : ∀ (n : ℤ) (j : J) (y : (N j).X n), (ι j).f n y = 0 →
    ∃ (k : J) (h : j ≤ k), (t h).f n y = 0)
  (W : Finset ℤ) (hW : ∀ n : ℤ, n ∉ W → IsZero (E.X n))
  (hfp : ∀ n : ℤ, Module.FinitePresentation R (E.X n))

include htrans hcompat hsurj hzero hW hfp in
/-- **Surjectivity of `colim_j Hom_{K(R)}(E, N j) → Hom_{K(R)}(E, P)`.** Every map in the homotopy
category from a bounded complex of finitely presented modules into the colimit factors through
some stage.

A representing chain map is lifted degreewise at the finitely many degrees where `E` is nonzero,
which puts all the lifts at a common stage; the finitely many commutation identities that the
lifted family fails to satisfy each hold after one further step, so at a stage above all of them
the lifted family is a chain map. -/
theorem exists_descends_homotopy (g : (Qh R).obj E ⟶ (Qh R).obj P) :
    ∃ (j : J) (ψ : (Qh R).obj E ⟶ (Qh R).obj (N j)), ψ ≫ (Qh R).map (ι j) = g := by
  classical
  obtain ⟨φ, rfl⟩ := (Qh R).map_surjective g
  have hlift : ∀ n : ℤ, ∃ (j : J) (ψ : E.X n ⟶ (N j).X n), ψ ≫ (ι j).f n = φ.f n := by
    intro n
    have := hfp n
    exact exists_lift htrans hcompat hsurj hzero n n (φ.f n)
  choose a ψa hψa using hlift
  have : Nonempty J := ⟨a 0⟩
  obtain ⟨j₀, hj₀⟩ := Finset.exists_le (W.image a)
  have haj : ∀ n ∈ W, a n ≤ j₀ := fun n hn => hj₀ _ (Finset.mem_image_of_mem _ hn)
  obtain ⟨u, hu_pos, hu_neg⟩ : ∃ u : ∀ n : ℤ, E.X n ⟶ (N j₀).X n,
      (∀ (n : ℤ) (hn : n ∈ W), u n = ψa n ≫ (t (haj n hn)).f n) ∧ ∀ n : ℤ, n ∉ W → u n = 0 :=
    ⟨fun n => if hn : n ∈ W then ψa n ≫ (t (haj n hn)).f n else 0,
      fun n hn => by simp [hn], fun n hn => by simp [hn]⟩
  have hu : ∀ n : ℤ, u n ≫ (ι j₀).f n = φ.f n := by
    intro n
    by_cases hn : n ∈ W
    · rw [hu_pos n hn, Category.assoc, t_comp_ι hcompat, hψa n]
    · exact (hW n hn).eq_of_src _ _
  -- the lifted family commutes with the differentials after one more step
  have hfix : ∀ n : ℤ, ∃ (k : J) (h : j₀ ≤ k),
      (u n ≫ (N j₀).d n (n + 1)) ≫ (t h).f (n + 1) =
        (E.d n (n + 1) ≫ u (n + 1)) ≫ (t h).f (n + 1) := by
    intro n
    by_cases hn : n ∈ W
    · have := hfp n
      refine exists_le_comp_eq htrans hzero n (n + 1) _ _ ?_
      have h1 : (u n ≫ (N j₀).d n (n + 1)) ≫ (ι j₀).f (n + 1) = φ.f n ≫ P.d n (n + 1) := by
        rw [Category.assoc, ← (ι j₀).comm n (n + 1), ← Category.assoc, hu n]
      have h2 : (E.d n (n + 1) ≫ u (n + 1)) ≫ (ι j₀).f (n + 1) = E.d n (n + 1) ≫ φ.f (n + 1) := by
        rw [Category.assoc, hu (n + 1)]
      rw [h1, h2]
      exact φ.comm n (n + 1)
    · exact ⟨j₀, le_rfl, (hW n hn).eq_of_src _ _⟩
  choose b hb hbeq using hfix
  obtain ⟨K, hK⟩ := Finset.exists_le (insert j₀ (W.image b))
  have hj₀K : j₀ ≤ K := hK j₀ (Finset.mem_insert_self _ _)
  have hbK : ∀ n ∈ W, b n ≤ K := fun n hn =>
    hK _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hn))
  have hcomm : ∀ i j : ℤ, (ComplexShape.up ℤ).Rel i j →
      (u i ≫ (t hj₀K).f i) ≫ (N K).d i j = E.d i j ≫ (u j ≫ (t hj₀K).f j) := by
    intro i j hij
    obtain rfl : j = i + 1 := hij.symm
    by_cases hi : i ∈ W
    · have key := congrArg (fun w => w ≫ (t (hbK i hi)).f (i + 1)) (hbeq i)
      simp only [Category.assoc, t_comp_t htrans] at key
      have g1 : (u i ≫ (t hj₀K).f i) ≫ (N K).d i (i + 1)
          = (u i ≫ (N j₀).d i (i + 1)) ≫ (t hj₀K).f (i + 1) := by
        rw [Category.assoc, (t hj₀K).comm i (i + 1), ← Category.assoc]
      have g2 : E.d i (i + 1) ≫ (u (i + 1) ≫ (t hj₀K).f (i + 1))
          = (E.d i (i + 1) ≫ u (i + 1)) ≫ (t hj₀K).f (i + 1) := (Category.assoc _ _ _).symm
      rw [g1, g2]
      exact key
    · exact (hW i hi).eq_of_src _ _
  refine ⟨K, (Qh R).map { f := fun n => u n ≫ (t hj₀K).f n, comm' := hcomm }, ?_⟩
  rw [← Functor.map_comp]
  congr 1
  refine HomologicalComplex.hom_ext _ _ fun n => ?_
  change (u n ≫ (t hj₀K).f n) ≫ (ι K).f n = φ.f n
  rw [Category.assoc, t_comp_ι hcompat]
  exact hu n

include htrans hcompat hsurj hzero hW hfp in
/-- **Injectivity of `colim_j Hom_{K(R)}(E, N j) → Hom_{K(R)}(E, P)`, at one stage.** Two maps in
the homotopy category out of a bounded complex of finitely presented modules into one stage which
become equal in the colimit are already equal at a later stage.

Equality in the homotopy category is a homotopy, and a homotopy is a `(-1)`-cochain `z` with
`δ z` the difference of the two maps. That cochain is lifted degreewise at the finitely many
degrees where `E` is nonzero, and the finitely many clauses of the resulting cochain identity
each hold after one further step, so at a stage above all of them the lifted cochain is a
homotopy. -/
theorem exists_le_eq_of_eq_homotopy_same {j : J}
    (ψ₁ ψ₂ : (Qh R).obj E ⟶ (Qh R).obj (N j))
    (h : ψ₁ ≫ (Qh R).map (ι j) = ψ₂ ≫ (Qh R).map (ι j)) :
    ∃ (k : J) (hjk : j ≤ k), ψ₁ ≫ (Qh R).map (t hjk) = ψ₂ ≫ (Qh R).map (t hjk) := by
  classical
  obtain ⟨φ₁, rfl⟩ := (Qh R).map_surjective ψ₁
  obtain ⟨φ₂, rfl⟩ := (Qh R).map_surjective ψ₂
  have hH : (Qh R).map (φ₁ ≫ ι j) = (Qh R).map (φ₂ ≫ ι j) := by
    rw [Functor.map_comp, Functor.map_comp]; exact h
  obtain ⟨z, hz⟩ := Cochain.equivHomotopy (φ₁ ≫ ι j) (φ₂ ≫ ι j)
    (HomotopyCategory.homotopyOfEq _ _ hH)
  -- lift the cochain degreewise
  have hlift : ∀ (p q : ℤ) (hpq : p + (-1) = q), ∃ (cc : J) (ww : E.X p ⟶ (N cc).X q),
      ww ≫ (ι cc).f q = z.v p q hpq := by
    intro p q hpq
    have := hfp p
    exact exists_lift htrans hcompat hsurj hzero p q (z.v p q hpq)
  choose c w hw using hlift
  have : Nonempty J := ⟨j⟩
  set c' : ℤ → J := fun p => c p (p - 1) (by omega) with hc'
  obtain ⟨l, hl⟩ := Finset.exists_le (insert j (W.image c'))
  have hjl : j ≤ l := hl j (Finset.mem_insert_self _ _)
  have hcl : ∀ (p q : ℤ) (hpq : p + (-1) = q), p ∈ W → c p q hpq ≤ l := by
    intro p q hpq hp
    obtain rfl : q = p - 1 := by omega
    exact hl _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp))
  -- the lifted cochain at stage `l`
  set z' : Cochain E (N l) (-1) := Cochain.mk (fun p q hpq =>
    if hp : p ∈ W then w p q hpq ≫ (t (hcl p q hpq hp)).f q else 0) with hz'
  have hz'v : ∀ (p q : ℤ) (hpq : p + (-1) = q), z'.v p q hpq ≫ (ι l).f q = z.v p q hpq := by
    intro p q hpq
    by_cases hp : p ∈ W
    · rw [hz']
      simp only [Cochain.mk_v, hp, dite_true, Category.assoc, t_comp_ι hcompat]
      exact hw p q hpq
    · exact (hW p hp).eq_of_src _ _
  have hz'comp : z'.comp (Cochain.ofHom (ι l)) (add_zero _) = z := by
    refine Cochain.ext _ _ fun p q hpq => ?_
    rw [Cochain.comp_v _ _ _ p q q hpq (add_zero q), Cochain.ofHom_v]
    exact hz'v p q hpq
  -- the cochain identity holds at stage `l` after mapping to the colimit
  have hcolim : ∀ p : ℤ,
      ((φ₁ ≫ t hjl).f p) ≫ (ι l).f p =
        ((δ (-1) 0 z').v p p (add_zero p) + (φ₂ ≫ t hjl).f p) ≫ (ι l).f p := by
    intro p
    have hzp := Cochain.congr_v hz p p (add_zero p)
    simp only [Cochain.ofHom_v, Cochain.add_v] at hzp
    have hδ : (δ (-1) 0 z').v p p (add_zero p) ≫ (ι l).f p = (δ (-1) 0 z).v p p (add_zero p) := by
      rw [← hz'comp, δ_comp_ofHom, Cochain.comp_v _ _ _ p p p (add_zero p) (add_zero p),
        Cochain.ofHom_v]
    rw [Preadditive.add_comp, hδ]
    simp only [HomologicalComplex.comp_f, Category.assoc, t_comp_ι hcompat]
    simpa only [HomologicalComplex.comp_f] using hzp
  -- each clause holds at a later stage; collect the stages
  have hfix : ∀ p : ℤ, ∃ (k : J) (hlk : l ≤ k),
      ((φ₁ ≫ t hjl).f p) ≫ (t hlk).f p =
        ((δ (-1) 0 z').v p p (add_zero p) + (φ₂ ≫ t hjl).f p) ≫ (t hlk).f p := by
    intro p
    by_cases hp : p ∈ W
    · have := hfp p
      exact exists_le_comp_eq htrans hzero p p _ _ (hcolim p)
    · exact ⟨l, le_rfl, (hW p hp).eq_of_src _ _⟩
  choose b hb hbeq using hfix
  obtain ⟨k, hk⟩ := Finset.exists_le (insert l (W.image b))
  have hlk : l ≤ k := hk l (Finset.mem_insert_self _ _)
  have hbk : ∀ p ∈ W, b p ≤ k := fun p hp =>
    hk _ (Finset.mem_insert_of_mem (Finset.mem_image_of_mem _ hp))
  have hstage : ∀ p : ℤ,
      ((φ₁ ≫ t hjl).f p) ≫ (t hlk).f p =
        ((δ (-1) 0 z').v p p (add_zero p) + (φ₂ ≫ t hjl).f p) ≫ (t hlk).f p := by
    intro p
    by_cases hp : p ∈ W
    · have key := congrArg (fun v => v ≫ (t (hbk p hp)).f p) (hbeq p)
      simpa only [Category.assoc, t_comp_t htrans] using key
    · exact (hW p hp).eq_of_src _ _
  -- assemble the homotopy at stage `k`
  have hfinal : Cochain.ofHom (φ₁ ≫ t (hjl.trans hlk))
      = δ (-1) 0 (z'.comp (Cochain.ofHom (t hlk)) (add_zero _))
        + Cochain.ofHom (φ₂ ≫ t (hjl.trans hlk)) := by
    refine Cochain.ext₀ _ _ fun p => ?_
    rw [Cochain.add_v, δ_comp_ofHom, Cochain.comp_v _ _ _ p p p (add_zero p) (add_zero p),
      Cochain.ofHom_v, Cochain.ofHom_v, Cochain.ofHom_v]
    have hs := hstage p
    simp only [HomologicalComplex.comp_f, Category.assoc, t_comp_t htrans,
      Preadditive.add_comp] at hs ⊢
    exact hs
  refine ⟨k, hjl.trans hlk, ?_⟩
  rw [← Functor.map_comp, ← Functor.map_comp]
  exact HomotopyCategory.eq_of_homotopy _ _ ((Cochain.equivHomotopy _ _).symm ⟨_, hfinal⟩)

include htrans hcompat hsurj hzero hW hfp in
/-- **Injectivity of `colim_j Hom_{K(R)}(E, N j) → Hom_{K(R)}(E, P)`.** Two maps in the homotopy
category out of a bounded complex of finitely presented modules, from two possibly different
stages, which become equal in the colimit already agree at a common later stage. -/
theorem exists_le_eq_of_eq_homotopy {i j : J}
    (ψ₁ : (Qh R).obj E ⟶ (Qh R).obj (N i)) (ψ₂ : (Qh R).obj E ⟶ (Qh R).obj (N j))
    (h : ψ₁ ≫ (Qh R).map (ι i) = ψ₂ ≫ (Qh R).map (ι j)) :
    ∃ (k : J) (hik : i ≤ k) (hjk : j ≤ k),
      ψ₁ ≫ (Qh R).map (t hik) = ψ₂ ≫ (Qh R).map (t hjk) := by
  obtain ⟨l, hil, hjl⟩ := directed_of (· ≤ ·) i j
  have hmid : (ψ₁ ≫ (Qh R).map (t hil)) ≫ (Qh R).map (ι l)
      = (ψ₂ ≫ (Qh R).map (t hjl)) ≫ (Qh R).map (ι l) := by
    rw [Category.assoc, Category.assoc, ← Functor.map_comp, ← Functor.map_comp,
      hcompat hil, hcompat hjl]
    exact h
  obtain ⟨k, hlk, hkey⟩ := exists_le_eq_of_eq_homotopy_same htrans hcompat hsurj hzero W hW hfp
    (ψ₁ ≫ (Qh R).map (t hil)) (ψ₂ ≫ (Qh R).map (t hjl)) hmid
  refine ⟨k, hil.trans hlk, hjl.trans hlk, ?_⟩
  rw [show t (hil.trans hlk) = t hil ≫ t hlk from (htrans hil hlk).symm,
    show t (hjl.trans hlk) = t hjl ≫ t hlk from (htrans hjl hlk).symm,
    Functor.map_comp, Functor.map_comp, ← Category.assoc, ← Category.assoc]
  exact hkey

end Main

section Derived

variable [HasDerivedCategory.{w} (ModuleCat.{u} R)]
  (htrans : ∀ ⦃i j k : J⦄ (h : i ≤ j) (h' : j ≤ k), t h ≫ t h' = t (h.trans h'))
  (hcompat : ∀ ⦃i j : J⦄ (h : i ≤ j), t h ≫ ι j = ι i)
  (hsurj : ∀ (n : ℤ) (x : P.X n), ∃ (j : J) (y : (N j).X n), (ι j).f n y = x)
  (hzero : ∀ (n : ℤ) (j : J) (y : (N j).X n), (ι j).f n y = 0 →
    ∃ (k : J) (h : j ≤ k), (t h).f n y = 0)
  (W : Finset ℤ) (hW : ∀ n : ℤ, n ∉ W → IsZero (E.X n))
  (hfp : ∀ n : ℤ, Module.FinitePresentation R (E.X n))
  (d : ℤ) [E.IsStrictlyLE d] [∀ n : ℤ, Projective (E.X n)]

include htrans hcompat hsurj hzero hW hfp d in
/-- **Surjectivity of `colim_j Hom_{D(R)}(E, N j) → Hom_{D(R)}(E, P)`** for `E` a bounded complex
of projective, finitely presented modules.

Such an `E` is K-projective, so the localization from the homotopy category to the derived
category is bijective on maps out of it and the homotopy-category statement transfers. -/
theorem exists_descends_derived
    (g : DerivedCategory.Qh.obj ((Qh R).obj E) ⟶ DerivedCategory.Qh.obj ((Qh R).obj P)) :
    ∃ (j : J) (ψ : DerivedCategory.Qh.obj ((Qh R).obj E) ⟶
      DerivedCategory.Qh.obj ((Qh R).obj (N j))),
      ψ ≫ DerivedCategory.Qh.map ((Qh R).map (ι j)) = g := by
  have : E.IsKProjective := CochainComplex.isKProjective_of_projective E d
  obtain ⟨g', hg'⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective E ((Qh R).obj P)).surjective g
  obtain ⟨j, ψ, hψ⟩ := exists_descends_homotopy htrans hcompat hsurj hzero W hW hfp g'
  exact ⟨j, DerivedCategory.Qh.map ψ, by rw [← Functor.map_comp, hψ, hg']⟩

include htrans hcompat hsurj hzero hW hfp d in
/-- **Injectivity of `colim_j Hom_{D(R)}(E, N j) → Hom_{D(R)}(E, P)`** for `E` a bounded complex
of projective, finitely presented modules. -/
theorem exists_le_eq_of_eq_derived {i j : J}
    (ψ₁ : DerivedCategory.Qh.obj ((Qh R).obj E) ⟶ DerivedCategory.Qh.obj ((Qh R).obj (N i)))
    (ψ₂ : DerivedCategory.Qh.obj ((Qh R).obj E) ⟶ DerivedCategory.Qh.obj ((Qh R).obj (N j)))
    (h : ψ₁ ≫ DerivedCategory.Qh.map ((Qh R).map (ι i))
      = ψ₂ ≫ DerivedCategory.Qh.map ((Qh R).map (ι j))) :
    ∃ (k : J) (hik : i ≤ k) (hjk : j ≤ k),
      ψ₁ ≫ DerivedCategory.Qh.map ((Qh R).map (t hik))
        = ψ₂ ≫ DerivedCategory.Qh.map ((Qh R).map (t hjk)) := by
  have : E.IsKProjective := CochainComplex.isKProjective_of_projective E d
  obtain ⟨χ₁, rfl⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective E ((Qh R).obj (N i))).surjective ψ₁
  obtain ⟨χ₂, rfl⟩ :=
    (CochainComplex.IsKProjective.Qh_map_bijective E ((Qh R).obj (N j))).surjective ψ₂
  have h' : χ₁ ≫ (Qh R).map (ι i) = χ₂ ≫ (Qh R).map (ι j) := by
    refine (CochainComplex.IsKProjective.Qh_map_bijective E ((Qh R).obj P)).injective ?_
    rw [Functor.map_comp, Functor.map_comp]
    exact h
  obtain ⟨k, hik, hjk, hkey⟩ :=
    exists_le_eq_of_eq_homotopy htrans hcompat hsurj hzero W hW hfp χ₁ χ₂ h'
  exact ⟨k, hik, hjk, by rw [← Functor.map_comp, ← Functor.map_comp, hkey]⟩

end Derived

end Stacks.FilteredColimitHom

end
