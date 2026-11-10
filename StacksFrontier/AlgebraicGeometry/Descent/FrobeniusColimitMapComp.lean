module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitMap

/-!
# Composing the functors induced on the colimit category along an endofunctor

Let `F : C ⥤ C`, `F' : C' ⥤ C'` and `F'' : C'' ⥤ C''` be endofunctors, and let `Φ : C ⥤ C'` and
`Ψ : C' ⥤ C''` commute with them up to natural isomorphisms `α : F ⋙ Φ ≅ Φ ⋙ F'` and
`β : F' ⋙ Ψ ≅ Ψ ⋙ F''`. The functor `colim_F C ⥤ colim_{F'} C'` which `Φ` and `α` induce is
`CategoryTheory.EndoColim.map`, built in
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitMap`. This file proves the two
functorialities of that construction:

* it is compatible with composition — the composite of the functors induced by `Φ` and by `Ψ`
  is the functor induced by `Φ ⋙ Ψ`, together with the comparison for the composite;
* it is compatible with an isomorphism of the inducing functor — an isomorphism `c : Φ ≅ Φ'`
  compatible with `α` and `α'` induces an isomorphism of the two induced functors.

Both need the action of the induced functor on a morphism between two objects of `colim_F C`
presented at *distinct* stages, which
`StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitMap` computes only at a common stage;
`CategoryTheory.EndoColim.map_map_of'` is that computation in general, and is the engine of the
file.

## Main definitions

* `CategoryTheory.EndoColim.transportHom'`: the morphism between iterates of `F'` which a
  morphism between iterates of `F` with *distinct* exponents induces.
* `CategoryTheory.EndoColim.compComm`: **the comparison `F ⋙ (Φ ⋙ Ψ) ≅ (Φ ⋙ Ψ) ⋙ F''` for a
  composite** of two functors each commuting with the endofunctors.
* `CategoryTheory.EndoColim.mapCompMapIso`: **the induced functors compose**, as an isomorphism
  of functors `colim_F C ⥤ colim_{F''} C''`.
* `CategoryTheory.EndoColim.mapCongrIso`: **an isomorphism of the inducing functor induces an
  isomorphism of the induced functors.**

## Main results

* `CategoryTheory.EndoColim.map_map_of'`: **the induced functor sends the morphism presented at
  level `k` by `f` between objects at the stages `n` and `m` to the morphism presented at level
  `k` by `Φ f`, conjugated by the iterated comparison.**
* `CategoryTheory.EndoColim.squareIter_compComm` and
  `CategoryTheory.EndoColim.transportHom'_comp`: the iterated comparison of a composite is the
  composite of the iterated comparisons, and likewise for the induced morphisms between
  iterates.
* `CategoryTheory.EndoColim.map_comp_map`: **the induced functors compose**, as an equality of
  functors.
* `CategoryTheory.EndoColim.squareIter_congr` and
  `CategoryTheory.EndoColim.transportHom'_congr`: an isomorphism of the inducing functor,
  compatible with the two comparisons, is compatible with the iterated comparisons and with
  the induced morphisms between iterates.

## Implementation notes

A morphism `(E, n) ⟶ (G, m)` of `colim_F C` presented at level `k` is a morphism
`F^{m + k}E ⟶ F^{n + k}G` of `C`, whose two exponents are distinct unless the two stages are.
`CategoryTheory.EndoColim.transportHom` is defined only for a morphism between two iterates
with the same exponent, so the computation of the induced functor on such a morphism needs the
two-exponent version `CategoryTheory.EndoColim.transportHom'`, of which it is the special case
`CategoryTheory.EndoColim.transportHom'_self`. Where
`CategoryTheory.EndoColim.map_map_of` conjugates by the iterated stage shift at one stage, the
general computation conjugates by it at the two stages `n + (m + k)` and `m + (n + k)`: these
are equal as numbers but not as terms, and the comparison of the stage functors at them which
`CategoryTheory.EndoColim.Pseudococone.mapAt` inserts is the stage cast
`CategoryTheory.EndoColim.stageCastIso`. The cast is moved out of the middle of the composite
by `CategoryTheory.EndoColim.stageCastIso_hom_comp_stageHomOf`, after which the three factors
between the two stage shifts merge into one and
`CategoryTheory.EndoColim.objShiftIso_conj'` applies.

Naturality of the two isomorphisms built here is therefore proved by presenting the morphism of
`colim_F C` at a level with `CategoryTheory.EndoColim.Hom.exists_of` — at arbitrary stages,
which is what `Iso.ext` and `CategoryTheory.Functor.hext` quantify over — rewriting both sides
with `CategoryTheory.EndoColim.map_map_of'`, and comparing the two presenting morphisms of
`C'`. For the composite the two presentations are at the same level and the comparison is
`CategoryTheory.EndoColim.transportHom'_comp`, so the isomorphism is an equality of functors
and `CategoryTheory.EndoColim.mapCompMapIso` is the identity on every object. For an
isomorphism of the inducing functor the components are not identities, and the two general
lemmas `CategoryTheory.EndoColim.Hom.of_comp_stageHomOf` and
`CategoryTheory.EndoColim.stageHomOf_comp_Hom_of` bring the two sides of the naturality square
into the form `CategoryTheory.EndoColim.Hom.of` applied to a composite in `C'`.

## References

* [Stacks Project, Tag 0EXA](https://stacks.math.columbia.edu/tag/0EXA)
* [Stacks Project, Tag 0EXC](https://stacks.math.columbia.edu/tag/0EXC)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u u₂ u₃

namespace CategoryTheory.EndoColim

variable {C : Type u} [Category.{v} C] {C' : Type u₂} [Category.{v} C']
  {C'' : Type u₃} [Category.{v} C'']

/-! ### Comparisons between iterates with distinct exponents -/

/-- **An iterate of `F` applied to a morphism between two iterates of `F`, transported, is a
raise of that morphism**, whatever exponents the two sides pass through, as soon as the iterate
and the raise amount agree. This is
`CategoryTheory.EndoColim.eqToHom_comp_endoIter_map_comp_eqToHom_eq` for a morphism whose source
and target are iterates with distinct exponents. -/
lemma eqToHom_comp_endoIter_map_comp_eqToHom_eq' (F : C ⥤ C) {a b : ℕ} {E G : C}
    (h : (F.endoIter a).obj E ⟶ (F.endoIter b).obj G) {N j q s q' s' : ℕ}
    (hj : N = j) (c₁ : N = q') (c₂ : N = s') (d₁ : a + j = q) (d₂ : b + j = s)
    (p : (F.endoIter q).obj E = (F.endoIter q').obj ((F.endoIter a).obj E))
    (r : (F.endoIter s').obj ((F.endoIter b).obj G) = (F.endoIter s).obj G) :
    eqToHom p ≫ endoHomCast c₁ c₂ ((F.endoIter N).map h) ≫ eqToHom r =
      endoHomCast d₁ d₂ (endoRaise h j) := by
  subst hj; subst c₁; subst c₂; subst d₁; subst d₂
  exact (endoRaise_eq_eqToHom_endoIter_map F h N p r).symm

/-- **A transported raise, followed by a transported iterate of a morphism of `C`, gives the
same morphism when the raise amounts and the iterates agree.** The two composites may run
through different exponents in the middle. -/
lemma endoHomCast_endoRaise_comp_endoIter_map_eq (F : C ⥤ C) {m n : ℕ} {E G H : C}
    (f : (F.endoIter m).obj E ⟶ (F.endoIter n).obj G) (g : G ⟶ H)
    {j j' N N' : ℕ} (hj : j = j') (hN : N = N') {q t t' w : ℕ}
    (a₁ : m + j = q) (a₂ : n + j = t) (a₃ : N = t) (a₄ : N = w)
    (b₁ : m + j' = q) (b₂ : n + j' = t') (b₃ : N' = t') (b₄ : N' = w) :
    endoHomCast a₁ a₂ (endoRaise f j) ≫ endoHomCast a₃ a₄ ((F.endoIter N).map g) =
      endoHomCast b₁ b₂ (endoRaise f j') ≫ endoHomCast b₃ b₄ ((F.endoIter N').map g) := by
  subst hj; subst hN
  obtain rfl : t = t' := by omega
  rfl

/-- **A transported iterate of a morphism of `C`, followed by a transported raise, gives the
same morphism when the iterates and the raise amounts agree.** The two composites may run
through different exponents in the middle. -/
lemma endoHomCast_endoIter_map_comp_endoRaise_eq (F : C ⥤ C) {m n : ℕ} {E G H : C}
    (g : E ⟶ G) (f : (F.endoIter m).obj G ⟶ (F.endoIter n).obj H)
    {N N' j j' : ℕ} (hN : N = N') (hj : j = j') {q t t' w : ℕ}
    (a₁ : N = q) (a₂ : N = t) (a₃ : m + j = t) (a₄ : n + j = w)
    (b₁ : N' = q) (b₂ : N' = t') (b₃ : m + j' = t') (b₄ : n + j' = w) :
    endoHomCast a₁ a₂ ((F.endoIter N).map g) ≫ endoHomCast a₃ a₄ (endoRaise f j) =
      endoHomCast b₁ b₂ ((F.endoIter N').map g) ≫ endoHomCast b₃ b₄ (endoRaise f j') := by
  subst hN; subst hj
  obtain rfl : t = t' := by omega
  rfl

/-! ### The cast between two equal stages -/

/-- The cast between a stage and itself is the identity. -/
private lemma stageCastIso_hom_rfl (F : C ⥤ C) (E : C) (a : ℕ) :
    (stageCastIso F E (rfl : a = a)).hom = 𝟙 (⟨E, a⟩ : EndoColim F) := by
  simp [stageCastIso]

/-- **The isomorphism between two equal stages of one object is presented at level `0`** by the
transport of objects comparing the two iterates. -/
lemma stageCastIso_hom_eq (F : C ⥤ C) (E : C) {a b : ℕ} (h : a = b)
    (q : (F.endoIter (b + 0)).obj E = (F.endoIter (a + 0)).obj E) :
    (stageCastIso F E h).hom = Hom.of 0 (eqToHom q) := by
  subst h
  rw [stageCastIso_hom_rfl, eqToHom_refl]
  exact (Hom.of_id (⟨E, a⟩ : EndoColim F) 0).symm

/-- **The cast between two equal stages is natural**: it commutes with the stage functor
applied to a morphism of `C`. -/
lemma stageCastIso_hom_comp_stageHomOf (F : C ⥤ C) {a b : ℕ} (h : a = b) {Y Z : C} (g : Y ⟶ Z) :
    (stageCastIso F Y h).hom ≫ stageHomOf F b g =
      stageHomOf F a g ≫ (stageCastIso F Z h).hom := by
  subst h
  rw [stageCastIso_hom_rfl, stageCastIso_hom_rfl, Category.id_comp, Category.comp_id]

/-! ### Conjugating by the iterated stage shift at two stages -/

/-- **Conjugating by the iterated stage shift at two stages turns the stage functor applied to
a morphism of `C` between iterates into the morphism of `colim_F C` presented at that level.**
This is `CategoryTheory.EndoColim.objShiftIso_conj` for two objects placed at distinct stages,
where the two shifts land at the two stages `n + (m + k)` and `m + (n + k)` — equal as numbers,
distinct as terms — and the cast between them enters. -/
lemma objShiftIso_conj' (F : C ⥤ C) (n m k : ℕ) (hnm : n + (m + k) = m + (n + k)) {E G : C}
    (h : (F.endoIter (m + k)).obj E ⟶ (F.endoIter (n + k)).obj G) :
    (objShiftIso F n (m + k) E).inv ≫ stageHomOf F (n + (m + k)) h ≫
          (stageCastIso F ((F.endoIter (n + k)).obj G) hnm).hom ≫
        (objShiftIso F m (n + k) G).hom =
      (Hom.of k h : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, m⟩) := by
  have hp : (F.endoIter (n + (m + k) + 0)).obj E =
      (F.endoIter (n + 0)).obj ((F.endoIter (m + k)).obj E) :=
    (endoIter_obj_endoIter_obj_of_eq F (show m + k + (n + 0) = n + (m + k) + 0 by omega) E).symm
  have hc : (F.endoIter (m + (n + k) + 0)).obj ((F.endoIter (n + k)).obj G) =
      (F.endoIter (n + (m + k) + 0)).obj ((F.endoIter (n + k)).obj G) := by
    rw [show m + (n + k) + 0 = n + (m + k) + 0 from by omega]
  have hr : (F.endoIter (m + 0)).obj ((F.endoIter (n + k)).obj G) =
      (F.endoIter (m + (n + k) + 0)).obj G :=
    endoIter_obj_endoIter_obj_of_eq F (show n + k + (m + 0) = m + (n + k) + 0 by omega) G
  rw [objShiftIso_inv_eq F n (m + k) E hp,
    stageCastIso_hom_eq F ((F.endoIter (n + k)).obj G) hnm hc,
    objShiftIso_hom_eq F m (n + k) G hr, stageHomOf]
  change Hom.of (n + (m + k) + 0 + (n + (m + k) + 0 + (m + (n + k) + 0 + 0))) _ = _
  refine Hom.of_eq_of _ _ 0 (3 * n + 3 * m + 2 * k) (by omega) ?_
  simp only [compHom, endoRaise_zero, endoRaise_comp, endoRaise_endoHomCast,
    endoRaise_eqToHom, endoRaise_endoIter_map, endoHomCast_comp_rfl, endoHomCast_endoHomCast,
    endoHomCast_eqToHom, eqToHom_trans]
  exact eqToHom_comp_endoIter_map_comp_eqToHom_eq' F h (by omega) (by omega) (by omega)
    (by omega) (by omega) _ _

/-! ### Composing a presented morphism with the stage functor -/

/-- **A morphism presented at a level, followed by the stage functor applied to a morphism of
`C`, is presented at the same level** by the composite in `C`. -/
lemma Hom.of_comp_stageHomOf (F : C ⥤ C) (n m k : ℕ) {E G H : C}
    (f : (F.endoIter (m + k)).obj E ⟶ (F.endoIter (n + k)).obj G) (g : G ⟶ H) :
    (Hom.of k f : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, m⟩) ≫ stageHomOf F m g =
      (Hom.of k (f ≫ (F.endoIter (n + k)).map g) : (⟨E, n⟩ : EndoColim F) ⟶ ⟨H, m⟩) := by
  change Hom.of (m + k + 0) _ = _
  refine Hom.of_eq_of _ _ 0 m (by omega) ?_
  simp only [compHom, endoRaise_zero, endoRaise_comp, endoRaise_endoIter_map,
    endoHomCast_comp_rfl, endoHomCast_endoHomCast]
  exact endoHomCast_endoRaise_comp_endoIter_map_eq F f g (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-- **The stage functor applied to a morphism of `C`, followed by a morphism presented at a
level, is presented at the same level** by the composite in `C`. -/
lemma stageHomOf_comp_Hom_of (F : C ⥤ C) (n m k : ℕ) {E G H : C} (g : E ⟶ G)
    (f : (F.endoIter (m + k)).obj G ⟶ (F.endoIter (n + k)).obj H) :
    stageHomOf F n g ≫ (Hom.of k f : (⟨G, n⟩ : EndoColim F) ⟶ ⟨H, m⟩) =
      (Hom.of k ((F.endoIter (m + k)).map g ≫ f) : (⟨E, n⟩ : EndoColim F) ⟶ ⟨H, m⟩) := by
  change Hom.of (n + 0 + k) _ = _
  refine Hom.of_eq_of _ _ 0 n (by omega) ?_
  simp only [compHom, endoRaise_zero, endoRaise_comp, endoRaise_endoIter_map,
    endoHomCast_comp_rfl, endoHomCast_endoHomCast]
  exact endoHomCast_endoIter_map_comp_endoRaise_eq F g f (by omega) (by omega) (by omega)
    (by omega) (by omega) (by omega) (by omega) (by omega) (by omega) (by omega)

/-! ### The induced functor on a morphism between objects at distinct stages -/

section Map

variable (F : C ⥤ C) (F' : C' ⥤ C') (Φ : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F')

/-- The morphism of `C'` which a morphism of `C` between two iterates of `F` with distinct
exponents induces: the image of the morphism under `Φ`, conjugated by the iterated comparison
at the two exponents. -/
def transportHom' (a b : ℕ) {E G : C} (f : (F.endoIter a).obj E ⟶ (F.endoIter b).obj G) :
    (F'.endoIter a).obj (Φ.obj E) ⟶ (F'.endoIter b).obj (Φ.obj G) :=
  (squareIter F F' Φ α a E).hom ≫ Φ.map f ≫ (squareIter F F' Φ α b G).inv

/-- At equal exponents the induced morphism is
`CategoryTheory.EndoColim.transportHom`. -/
lemma transportHom'_self (a : ℕ) {E G : C}
    (f : (F.endoIter a).obj E ⟶ (F.endoIter a).obj G) :
    transportHom' F F' Φ α a a f = transportHom F F' Φ α a f := rfl

/-- The comparison of the stage functors at equal indices which the pseudo-cocone of `Φ`
carries is the cast between the two stages. -/
lemma mapPseudococone_stageHom_app {N M : ℕ} (h : N = M) (Y : C) :
    ((mapPseudococone F F' Φ α).stageHom h).app Y = (stageCastIso F' (Φ.obj Y) h).hom := by
  subst h
  rw [stageCastIso_hom_rfl, Pseudococone.stageHom_refl]
  rfl

/-- **The induced functor sends the morphism presented at level `k` by `f`, between objects
placed at the two stages `n` and `m`, to the morphism presented at level `k` by `Φ f`,
conjugated by the iterated comparison.** This is
`CategoryTheory.EndoColim.map_map_of` without the assumption that the two objects are placed at
one and the same stage. -/
lemma map_map_of' (n m k : ℕ) {E G : C}
    (f : (F.endoIter (m + k)).obj E ⟶ (F.endoIter (n + k)).obj G) :
    (map F F' Φ α).map (Hom.of k f : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, m⟩) =
      (Hom.of k (transportHom' F F' Φ α (m + k) (n + k) f) :
        (⟨Φ.obj E, n⟩ : EndoColim F') ⟶ ⟨Φ.obj G, m⟩) := by
  have hh : n + (m + k) = m + (n + k) := by omega
  have h1 : ((objShiftIso F' n (m + k) (Φ.obj E)).inv ≫
          stageHomOf F' (n + (m + k)) (squareIter F F' Φ α (m + k) E).hom) ≫
        stageHomOf F' (n + (m + k)) (Φ.map f) ≫
          (stageCastIso F' (Φ.obj ((F.endoIter (n + k)).obj G)) hh).hom ≫
            (stageHomOf F' (m + (n + k)) (squareIter F F' Φ α (n + k) G).inv ≫
              (objShiftIso F' m (n + k) (Φ.obj G)).hom) =
      (map F F' Φ α).map (Hom.of k f : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, m⟩) := by
    rw [← mapPseudococone_iterObjIso_inv, ← mapPseudococone_iterObjIso_hom,
      ← mapPseudococone_stageHom_app F F' Φ α hh ((F.endoIter (n + k)).obj G)]
    rfl
  refine h1.symm.trans ?_
  rw [transportHom']
  simp only [Category.assoc]
  rw [reassoc_of% (stageCastIso_hom_comp_stageHomOf F' hh (squareIter F F' Φ α (n + k) G).inv),
    ← reassoc_of% (stageHomOf_comp F' (n + (m + k)) (Φ.map f)
      (squareIter F F' Φ α (n + k) G).inv),
    ← reassoc_of% (stageHomOf_comp F' (n + (m + k)) (squareIter F F' Φ α (m + k) E).hom
      (Φ.map f ≫ (squareIter F F' Φ α (n + k) G).inv))]
  exact objShiftIso_conj' F' n m k hh _

end Map

/-! ### The comparison for a composite -/

section Comp

variable (F : C ⥤ C) (F' : C' ⥤ C') (F'' : C'' ⥤ C'') (Φ : C ⥤ C') (Ψ : C' ⥤ C'')
  (α : F ⋙ Φ ≅ Φ ⋙ F') (β : F' ⋙ Ψ ≅ Ψ ⋙ F'')

/-- The comparison for a composite of two functors each commuting with the endofunctors. -/
def compComm : F ⋙ (Φ ⋙ Ψ) ≅ (Φ ⋙ Ψ) ⋙ F'' :=
  (Functor.associator F Φ Ψ).symm ≪≫ Functor.isoWhiskerRight α Ψ ≪≫
    Functor.associator Φ F' Ψ ≪≫ Functor.isoWhiskerLeft Φ β ≪≫
      (Functor.associator Φ Ψ F'').symm

/-- The component of `CategoryTheory.EndoColim.compComm` at an object: `Ψ` applied to the
component of `α`, followed by the component of `β`. -/
@[simp]
lemma compComm_hom_app (E : C) :
    (compComm F F' F'' Φ Ψ α β).hom.app E = Ψ.map (α.hom.app E) ≫ β.hom.app (Φ.obj E) := by
  simp [compComm]

/-- The inverse component of `CategoryTheory.EndoColim.compComm` at an object: the inverse
component of `β`, followed by `Ψ` applied to the inverse component of `α`. -/
@[simp]
lemma compComm_inv_app (E : C) :
    (compComm F F' F'' Φ Ψ α β).inv.app E = β.inv.app (Φ.obj E) ≫ Ψ.map (α.inv.app E) := by
  simp [compComm]

/-- **The iterated comparison for a composite is the composite of the iterated
comparisons.** -/
lemma squareIter_compComm : ∀ (k : ℕ) (E : C),
    (squareIter F F'' (Φ ⋙ Ψ) (compComm F F' F'' Φ Ψ α β) k E).hom =
      (squareIter F' F'' Ψ β k (Φ.obj E)).hom ≫ Ψ.map (squareIter F F' Φ α k E).hom
  | 0, E => by
      change 𝟙 _ = 𝟙 _ ≫ Ψ.map (𝟙 _)
      rw [Ψ.map_id, Category.comp_id]
  | k + 1, E => by
      have ih := squareIter_compComm k E
      have hnat := β.inv.naturality (squareIter F F' Φ α k E).hom
      simp only [Functor.comp_map] at hnat
      change F''.map (squareIter F F'' (Φ ⋙ Ψ) (compComm F F' F'' Φ Ψ α β) k E).hom ≫
            (compComm F F' F'' Φ Ψ α β).inv.app ((F.endoIter k).obj E) =
          (F''.map (squareIter F' F'' Ψ β k (Φ.obj E)).hom ≫
              β.inv.app ((F'.endoIter k).obj (Φ.obj E))) ≫
            Ψ.map (F'.map (squareIter F F' Φ α k E).hom ≫
              α.inv.app ((F.endoIter k).obj E))
      rw [ih, compComm_inv_app, F''.map_comp, Ψ.map_comp]
      simp only [Category.assoc]
      rw [reassoc_of% hnat]

/-- The iterated comparison for a composite, as an equality of isomorphisms. -/
lemma squareIter_compComm_iso (k : ℕ) (E : C) :
    squareIter F F'' (Φ ⋙ Ψ) (compComm F F' F'' Φ Ψ α β) k E =
      squareIter F' F'' Ψ β k (Φ.obj E) ≪≫ Ψ.mapIso (squareIter F F' Φ α k E) :=
  Iso.ext (squareIter_compComm F F' F'' Φ Ψ α β k E)

/-- The inverse half of `CategoryTheory.EndoColim.squareIter_compComm`. -/
lemma squareIter_compComm_inv (k : ℕ) (E : C) :
    (squareIter F F'' (Φ ⋙ Ψ) (compComm F F' F'' Φ Ψ α β) k E).inv =
      Ψ.map (squareIter F F' Φ α k E).inv ≫ (squareIter F' F'' Ψ β k (Φ.obj E)).inv :=
  congrArg Iso.inv (squareIter_compComm_iso F F' F'' Φ Ψ α β k E)

/-- **The morphism between iterates induced by a composite is the composite of the induced
morphisms**, for a morphism between iterates with distinct exponents. -/
lemma transportHom'_comp (a b : ℕ) {E G : C}
    (f : (F.endoIter a).obj E ⟶ (F.endoIter b).obj G) :
    transportHom' F F'' (Φ ⋙ Ψ) (compComm F F' F'' Φ Ψ α β) a b f =
      transportHom' F' F'' Ψ β a b (transportHom' F F' Φ α a b f) := by
  rw [transportHom', transportHom', transportHom', squareIter_compComm,
    squareIter_compComm_inv]
  change _ ≫ Ψ.map (Φ.map f) ≫ _ = _ ≫ Ψ.map ((squareIter F F' Φ α a E).hom ≫
    Φ.map f ≫ (squareIter F F' Φ α b G).inv) ≫ _
  rw [Ψ.map_comp, Ψ.map_comp]
  simp only [Category.assoc]

/-- **The morphism between iterates induced by a composite is the composite of the induced
morphisms.** -/
lemma transportHom_comp (a : ℕ) {E G : C}
    (f : (F.endoIter a).obj E ⟶ (F.endoIter a).obj G) :
    transportHom F F'' (Φ ⋙ Ψ) (compComm F F' F'' Φ Ψ α β) a f =
      transportHom F' F'' Ψ β a (transportHom F F' Φ α a f) :=
  transportHom'_comp F F' F'' Φ Ψ α β a a f

/-- **The induced functors compose**, on a morphism presented at a level. -/
lemma map_comp_map_of (n m k : ℕ) {E G : C}
    (f : (F.endoIter (m + k)).obj E ⟶ (F.endoIter (n + k)).obj G) :
    (map F F' Φ α ⋙ map F' F'' Ψ β).map (Hom.of k f : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, m⟩) =
      (map F F'' (Φ ⋙ Ψ) (compComm F F' F'' Φ Ψ α β)).map
        (Hom.of k f : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, m⟩) := by
  have h₂ := map_map_of' F' F'' Ψ β n m k (transportHom' F F' Φ α (m + k) (n + k) f)
  have h₃ := map_map_of' F F'' (Φ ⋙ Ψ) (compComm F F' F'' Φ Ψ α β) n m k f
  rw [Functor.comp_map, map_map_of' F F' Φ α n m k f]
  refine h₂.trans (Eq.trans ?_ h₃.symm)
  exact congrArg (fun w : (F''.endoIter (m + k)).obj (Ψ.obj (Φ.obj E)) ⟶
      (F''.endoIter (n + k)).obj (Ψ.obj (Φ.obj G)) ↦
        (Hom.of k w : (⟨Ψ.obj (Φ.obj E), n⟩ : EndoColim F'') ⟶ ⟨Ψ.obj (Φ.obj G), m⟩))
    (transportHom'_comp F F' F'' Φ Ψ α β (m + k) (n + k) f).symm

/-- **The induced functors compose.** The functor induced by `Φ` followed by the functor
induced by `Ψ` is the functor induced by `Φ ⋙ Ψ`, with the comparison
`CategoryTheory.EndoColim.compComm` for the composite. -/
lemma map_comp_map :
    map F F' Φ α ⋙ map F' F'' Ψ β = map F F'' (Φ ⋙ Ψ) (compComm F F' F'' Φ Ψ α β) :=
  Functor.hext (fun _ ↦ rfl) fun A B u ↦ by
    obtain ⟨E, n⟩ := A
    obtain ⟨G, m⟩ := B
    obtain ⟨k, f, rfl⟩ := Hom.exists_of u
    exact heq_of_eq (map_comp_map_of F F' F'' Φ Ψ α β n m k f)

/-- **The induced functors compose**, as an isomorphism of functors. It is the identity on
every object of `colim_F C`. -/
def mapCompMapIso :
    map F F' Φ α ⋙ map F' F'' Ψ β ≅ map F F'' (Φ ⋙ Ψ) (compComm F F' F'' Φ Ψ α β) :=
  NatIso.ofComponents (fun _ ↦ Iso.refl _) fun {A B} u ↦ by
    obtain ⟨E, n⟩ := A
    obtain ⟨G, m⟩ := B
    obtain ⟨k, f, rfl⟩ := Hom.exists_of u
    refine (Category.comp_id _).trans (Eq.trans ?_ (Category.id_comp _).symm)
    exact map_comp_map_of F F' F'' Φ Ψ α β n m k f

/-- The components of `CategoryTheory.EndoColim.mapCompMapIso` are identities. -/
@[simp]
lemma mapCompMapIso_hom_app (A : EndoColim F) :
    (mapCompMapIso F F' F'' Φ Ψ α β).hom.app A = 𝟙 _ := rfl

end Comp

/-! ### The induced functor and an isomorphism of the inducing functor -/

section Congr

variable (F : C ⥤ C) (F' : C' ⥤ C') (Φ Φ' : C ⥤ C') (α : F ⋙ Φ ≅ Φ ⋙ F')
  (α' : F ⋙ Φ' ≅ Φ' ⋙ F') (c : Φ ≅ Φ')

/-- The compatibility of an isomorphism `c : Φ ≅ Φ'` with the two comparisons, at an object. -/
lemma congr_hom_app
    (hc : Functor.isoWhiskerLeft F c ≪≫ α' = α ≪≫ Functor.isoWhiskerRight c F') (E : C) :
    c.hom.app (F.obj E) ≫ α'.hom.app E = α.hom.app E ≫ F'.map (c.hom.app E) := by
  have h := congrArg (fun i : F ⋙ Φ ≅ Φ' ⋙ F' ↦ i.hom.app E) hc
  simpa using h

/-- The compatibility of an isomorphism `c : Φ ≅ Φ'` with the two comparisons, at an object and
in terms of their inverses. -/
lemma congr_inv_app
    (hc : Functor.isoWhiskerLeft F c ≪≫ α' = α ≪≫ Functor.isoWhiskerRight c F') (E : C) :
    F'.map (c.hom.app E) ≫ α'.inv.app E = α.inv.app E ≫ c.hom.app (F.obj E) := by
  rw [← cancel_epi (α.hom.app E), ← reassoc_of% (congr_hom_app F F' Φ Φ' α α' c hc E)]
  simp

/-- **An isomorphism of the inducing functor, compatible with the two comparisons, is
compatible with the iterated comparisons.** -/
lemma squareIter_congr
    (hc : Functor.isoWhiskerLeft F c ≪≫ α' = α ≪≫ Functor.isoWhiskerRight c F') :
    ∀ (k : ℕ) (E : C),
      (F'.endoIter k).map (c.hom.app E) ≫ (squareIter F F' Φ' α' k E).hom =
        (squareIter F F' Φ α k E).hom ≫ c.hom.app ((F.endoIter k).obj E)
  | 0, E => (Category.comp_id _).trans (Category.id_comp _).symm
  | k + 1, E => by
      have ih := squareIter_congr hc k E
      have key := congr_inv_app F F' Φ Φ' α α' c hc ((F.endoIter k).obj E)
      change F'.map ((F'.endoIter k).map (c.hom.app E)) ≫
            (F'.map (squareIter F F' Φ' α' k E).hom ≫ α'.inv.app ((F.endoIter k).obj E)) =
          (F'.map (squareIter F F' Φ α k E).hom ≫ α.inv.app ((F.endoIter k).obj E)) ≫
            c.hom.app (F.obj ((F.endoIter k).obj E))
      rw [← Category.assoc, ← F'.map_comp, ih, F'.map_comp, Category.assoc, Category.assoc,
        key]

/-- **An isomorphism of the inducing functor, compatible with the two comparisons, is
compatible with the morphisms between iterates which the two functors induce.** -/
lemma transportHom'_congr
    (hc : Functor.isoWhiskerLeft F c ≪≫ α' = α ≪≫ Functor.isoWhiskerRight c F')
    (a b : ℕ) {E G : C} (f : (F.endoIter a).obj E ⟶ (F.endoIter b).obj G) :
    transportHom' F F' Φ α a b f ≫ (F'.endoIter b).map (c.hom.app G) =
      (F'.endoIter a).map (c.hom.app E) ≫ transportHom' F F' Φ' α' a b f := by
  have hb : (squareIter F F' Φ α b G).inv ≫ (F'.endoIter b).map (c.hom.app G) =
      c.hom.app ((F.endoIter b).obj G) ≫ (squareIter F F' Φ' α' b G).inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc,
      ← squareIter_congr F F' Φ Φ' α α' c hc b G, Category.assoc, Iso.hom_inv_id,
      Category.comp_id]
  rw [transportHom', transportHom']
  simp only [Category.assoc]
  rw [hb, reassoc_of% (c.hom.naturality f),
    reassoc_of% (squareIter_congr F F' Φ Φ' α α' c hc a E)]

/-- **An isomorphism of the inducing functor, compatible with the two comparisons, induces an
isomorphism of the induced functors.** Its component at the object `(E, n)` is the stage-`n`
functor applied to the component of `c` at `E`. -/
def mapCongrIso
    (hc : Functor.isoWhiskerLeft F c ≪≫ α' = α ≪≫ Functor.isoWhiskerRight c F') :
    map F F' Φ α ≅ map F F' Φ' α' :=
  NatIso.ofComponents (fun A ↦ (stageFunctor F' A.stage).mapIso (c.app A.obj)) fun {A B} u ↦ by
    obtain ⟨E, n⟩ := A
    obtain ⟨G, m⟩ := B
    obtain ⟨k, f, rfl⟩ := Hom.exists_of u
    change (map F F' Φ α).map (Hom.of k f : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, m⟩) ≫
        stageHomOf F' m (c.hom.app G) =
      stageHomOf F' n (c.hom.app E) ≫
        (map F F' Φ' α').map (Hom.of k f : (⟨E, n⟩ : EndoColim F) ⟶ ⟨G, m⟩)
    rw [map_map_of' F F' Φ α n m k f, map_map_of' F F' Φ' α' n m k f]
    refine (Hom.of_comp_stageHomOf F' n m k
      (transportHom' F F' Φ α (m + k) (n + k) f) (c.hom.app G)).trans
      (Eq.trans ?_ (stageHomOf_comp_Hom_of F' n m k (c.hom.app E)
        (transportHom' F F' Φ' α' (m + k) (n + k) f)).symm)
    exact congrArg (fun w : (F'.endoIter (m + k)).obj (Φ.obj E) ⟶
        (F'.endoIter (n + k)).obj (Φ'.obj G) ↦
          (Hom.of k w : (⟨Φ.obj E, n⟩ : EndoColim F') ⟶ ⟨Φ'.obj G, m⟩))
      (transportHom'_congr F F' Φ Φ' α α' c hc (m + k) (n + k) f)

/-- The component of `CategoryTheory.EndoColim.mapCongrIso` at the object `(E, n)` is the
stage-`n` morphism induced by the component of `c` at `E`. -/
@[simp]
lemma mapCongrIso_hom_app
    (hc : Functor.isoWhiskerLeft F c ≪≫ α' = α ≪≫ Functor.isoWhiskerRight c F') (E : C)
    (n : ℕ) :
    (mapCongrIso F F' Φ Φ' α α' c hc).hom.app ⟨E, n⟩ = stageHomOf F' n (c.hom.app E) := rfl

end Congr

end CategoryTheory.EndoColim

end
