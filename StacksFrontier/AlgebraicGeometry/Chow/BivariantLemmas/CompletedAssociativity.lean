module

public import StacksFrontier.AlgebraicGeometry.Chow.BivariantComposition.AssociativityOfInvertible
public import StacksFrontier.AlgebraicGeometry.Chow.BivariantLemmas.CompletedOpenImmersionComposite

/-!
# Associativity of the composition of completed bivariant classes

Let `(S, δ)` be the base situation of chapter 42 of the Stacks Project and let `f : X ⟶ Y`,
`g : Y ⟶ Z` and `h : Z ⟶ W` be morphisms of schemes locally of finite type over `S`. The
composition of bivariant classes extends to the completed bivariant groups of Stacks 0FE0,
`A^*(X ⟶ Y)^∧ × A^*(Y ⟶ Z)^∧ ⟶ A^*(X ⟶ Z)^∧`
(`Stacks.Chow.completedBivariantCompositeOfInvertible`), and the extension is associative, as the
composition of Stacks 0B75 is (`Stacks.Chow.bivariantCompositeOfInvertible_assoc`).

## Main results

* `Stacks.Chow.directSumBilinear_assoc` — associativity of the convolution of graded groups along
  bilinear pairings, from associativity on homogeneous elements.
* `Stacks.Chow.completedAssoc_homogeneous` — the same on homogeneous classes, through the
  transports of the completed composition.
* `Stacks.Chow.completedBivariantCompositeOfInvertible_assoc` — `(c ∘ d) ∘ e = c ∘ (d ∘ e)` in
  `A^*(X ⟶ W)^∧`.

## References

* [Stacks Project, Tag 0FE0](https://stacks.math.columbia.edu/tag/0FE0)
* [Stacks Project, Tag 0B75](https://stacks.math.columbia.edu/tag/0B75)
* [Stacks Project, Tag 0B76](https://stacks.math.columbia.edu/tag/0B76)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u v

namespace Stacks.Chow

/-! ### Convolution bookkeeping -/

section Convolution

variable {A B D AB BD E A' B' E' : ℤ → Type v} [∀ n, AddCommGroup (A n)]
  [∀ n, AddCommGroup (B n)] [∀ n, AddCommGroup (D n)] [∀ n, AddCommGroup (AB n)]
  [∀ n, AddCommGroup (BD n)] [∀ n, AddCommGroup (E n)] [∀ n, AddCommGroup (A' n)]
  [∀ n, AddCommGroup (B' n)] [∀ n, AddCommGroup (E' n)]

/-- Two homogeneous elements of a direct sum in equal degrees that are heterogeneously equal are
equal. -/
theorem directSum_of_eq_of_heq {i j : ℤ} (hij : i = j) (x : E i) (y : E j) (hxy : x ≍ y) :
    DirectSum.of E i x = DirectSum.of E j y := by
  subst hij
  rw [eq_of_heq hxy]

/-- A degreewise isomorphism of the left factor is absorbed into the pairing. -/
theorem directSumBilinear_mapRange_left (m : ∀ p q, A' p →+ B q →+ E (p + q))
    (e : ∀ n, A n ≃+ A' n) (x : DirectSum ℤ A) (y : DirectSum ℤ B) :
    directSumBilinear m (DFinsupp.mapRange.addEquiv e x) y =
      directSumBilinear (fun p q ↦ (m p q).comp (e p).toAddMonoidHom) x y := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p a =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | of q b => simp only [mapRange_addEquiv_of, directSumBilinear_of_of]; rfl
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, AddMonoidHom.add_apply, h₁, h₂]

/-- A degreewise isomorphism of the right factor is absorbed into the pairing. -/
theorem directSumBilinear_mapRange_right (m : ∀ p q, A p →+ B' q →+ E (p + q))
    (e : ∀ n, B n ≃+ B' n) (x : DirectSum ℤ A) (y : DirectSum ℤ B) :
    directSumBilinear m x (DFinsupp.mapRange.addEquiv e y) =
      directSumBilinear (fun p q ↦ (m p q).compl₂ (e q).toAddMonoidHom)
        x y := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p a =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | of q b => simp only [mapRange_addEquiv_of, directSumBilinear_of_of]; rfl
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, AddMonoidHom.add_apply, h₁, h₂]

/-- A degreewise isomorphism of the target is absorbed into the pairing. -/
theorem mapRange_directSumBilinear (m : ∀ p q, A p →+ B q →+ E (p + q))
    (e : ∀ n, E n ≃+ E' n) (x : DirectSum ℤ A) (y : DirectSum ℤ B) :
    DFinsupp.mapRange.addEquiv e (directSumBilinear m x y) =
      directSumBilinear (fun p q ↦ (m p q).compr₂ (e (p + q)).toAddMonoidHom)
        x y := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | of p a =>
    induction y using DirectSum.induction_on with
    | zero => simp
    | of q b => simp only [directSumBilinear_of_of, mapRange_addEquiv_of]; rfl
    | add y₁ y₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | add x₁ x₂ h₁ h₂ => simp only [map_add, AddMonoidHom.add_apply, h₁, h₂]

/-- **Associativity of the convolution.** If two ways of pairing three graded groups agree on
homogeneous elements, up to the identification of the degrees `(p + q) + r` and `p + (q + r)`,
then the two iterated convolutions agree. -/
theorem directSumBilinear_assoc (m₁ : ∀ p q, A p →+ B q →+ AB (p + q))
    (m₂ : ∀ s r, AB s →+ D r →+ E (s + r)) (m₃ : ∀ q r, B q →+ D r →+ BD (q + r))
    (m₄ : ∀ p t, A p →+ BD t →+ E (p + t))
    (hm : ∀ p q r (a : A p) (b : B q) (d : D r),
      m₂ (p + q) r (m₁ p q a b) d ≍ m₄ p (q + r) a (m₃ q r b d))
    (x : DirectSum ℤ A) (y : DirectSum ℤ B) (z : DirectSum ℤ D) :
    directSumBilinear m₂ (directSumBilinear m₁ x y) z =
      directSumBilinear m₄ x (directSumBilinear m₃ y z) := by
  induction x using DirectSum.induction_on with
  | zero => simp
  | add x₁ x₂ h₁ h₂ => simp only [map_add, AddMonoidHom.add_apply, h₁, h₂]
  | of p a =>
  induction y using DirectSum.induction_on with
  | zero => simp
  | add y₁ y₂ h₁ h₂ => simp only [map_add, AddMonoidHom.add_apply, h₁, h₂]
  | of q b =>
  induction z using DirectSum.induction_on with
  | zero => simp
  | add z₁ z₂ h₁ h₂ => simp only [map_add, h₁, h₂]
  | of r d =>
  rw [directSumBilinear_of_of, directSumBilinear_of_of, directSumBilinear_of_of,
    directSumBilinear_of_of]
  exact directSum_of_eq_of_heq (add_assoc p q r) _ _ (hm p q r a b d)

/-- **Associativity of the convolution, through transports.** The form of
`Stacks.Chow.directSumBilinear_assoc` in which the inner composites, the outer composites and the
third factor are read through degreewise isomorphisms. -/
theorem directSumBilinear_assoc_of_mapRange {D' AB' BD' E₁ E₂ F : ℤ → Type v}
    [∀ n, AddCommGroup (D' n)] [∀ n, AddCommGroup (AB' n)] [∀ n, AddCommGroup (BD' n)]
    [∀ n, AddCommGroup (E₁ n)] [∀ n, AddCommGroup (E₂ n)] [∀ n, AddCommGroup (F n)]
    {F' : ℤ → Type v} [∀ n, AddCommGroup (F' n)]
    (m₁ : ∀ p q, A p →+ B q →+ AB (p + q)) (τ₁ : ∀ n, AB n ≃+ AB' n)
    (m₂ : ∀ s r, AB' s →+ D' r →+ E₁ (s + r)) (τ₂ : ∀ n, E₁ n ≃+ F' n) (φ : ∀ n, F' n ≃+ F n)
    (m₃ : ∀ q r, B q →+ D r →+ BD (q + r)) (τ₃ : ∀ n, BD n ≃+ BD' n)
    (m₄ : ∀ p t, A p →+ BD' t →+ E₂ (p + t)) (τ₄ : ∀ n, E₂ n ≃+ F n)
    (σ : ∀ n, D' n ≃+ D n) (x : DirectSum ℤ A) (y : DirectSum ℤ B) (z' : DirectSum ℤ D')
    (z : DirectSum ℤ D) (hz : DFinsupp.mapRange.addEquiv σ z' = z)
    (hm : ∀ p q r (a : A p) (b : B q) (d : D' r),
      φ (p + q + r) (τ₂ (p + q + r) (m₂ (p + q) r (τ₁ (p + q) (m₁ p q a b)) d)) ≍
        τ₄ (p + (q + r)) (m₄ p (q + r) a (τ₃ (q + r) (m₃ q r b (σ r d))))) :
    DFinsupp.mapRange.addEquiv φ (DFinsupp.mapRange.addEquiv τ₂
        (directSumBilinear m₂ (DFinsupp.mapRange.addEquiv τ₁ (directSumBilinear m₁ x y)) z')) =
      DFinsupp.mapRange.addEquiv τ₄
        (directSumBilinear m₄ x (DFinsupp.mapRange.addEquiv τ₃ (directSumBilinear m₃ y z))) := by
  subst hz
  rw [mapRange_directSumBilinear, mapRange_directSumBilinear, directSumBilinear_mapRange_left,
    directSumBilinear_mapRange_right m₄, mapRange_directSumBilinear,
    directSumBilinear_mapRange_right m₃]
  exact directSumBilinear_assoc _ _ _ _ (fun p q r a b d ↦ hm p q r a b d) x y z'

end Convolution

/-! ### Composites of classes for components indexed by equal components -/

section ComponentCongr

variable (C : ChowSituation.{u}) {V Z W : Scheme.{u}} (sV : V ⟶ C.S) [LocallyOfFiniteType sV]
  (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ] (sW : W ⟶ C.S) [LocallyOfFiniteType sW]
  [IsLocallyNoetherian Z] [IsLocallyNoetherian W] (h : Z ⟶ W) [LocallyOfFiniteType h]
  (hh : h ≫ sW = sZ)

/-- Bivariant classes for the restrictions of `h` to two equal connected components of `Z` are the
same group. -/
def bivariantClassSourceComponentCongr {u₁ u₂ : _root_.ConnectedComponents Z} (hu : u₁ = u₂)
    (n : ℤ) :
    BivariantClass C (gysinSystemOfInvertible C) ((Z.connectedComponentOpens u₁).ι ≫ sZ)
        ((W.connectedComponentOpens (h.continuous.connectedComponentsMap u₁)).ι ≫ sW)
        (h.resConnectedComponent u₁) (h.resConnectedComponent_comp_ι_comp hh u₁) n ≃+
      BivariantClass C (gysinSystemOfInvertible C) ((Z.connectedComponentOpens u₂).ι ≫ sZ)
        ((W.connectedComponentOpens (h.continuous.connectedComponentsMap u₂)).ι ≫ sW)
        (h.resConnectedComponent u₂) (h.resConnectedComponent_comp_ι_comp hh u₂) n := by
  subst hu
  exact AddEquiv.refl _

/-- The transport of `Stacks.Chow.bivariantClassSourceComponentCongr` changes nothing. -/
theorem bivariantClassSourceComponentCongr_heq {u₁ u₂ : _root_.ConnectedComponents Z}
    (hu : u₁ = u₂) (n : ℤ)
    (x : BivariantClass C (gysinSystemOfInvertible C) ((Z.connectedComponentOpens u₁).ι ≫ sZ)
        ((W.connectedComponentOpens (h.continuous.connectedComponentsMap u₁)).ι ≫ sW)
        (h.resConnectedComponent u₁) (h.resConnectedComponent_comp_ι_comp hh u₁) n) :
    bivariantClassSourceComponentCongr C sZ sW h hh hu n x ≍ x := by
  subst hu
  rfl

/-- Reading a completed class at two equal connected components of the source: the transport
along `Stacks.Chow.bivariantClassSourceComponentCongr` carries one to the other. -/
theorem mapRange_bivariantClassSourceComponentCongr
    (e : completedBivariantGroup C (gysinSystemOfInvertible C) sZ sW h hh)
    {u₁ u₂ : _root_.ConnectedComponents Z} (hu : u₁ = u₂) :
    DFinsupp.mapRange.addEquiv (bivariantClassSourceComponentCongr C sZ sW h hh hu) (e u₁) =
      e u₂ := by
  subst hu
  refine DirectSum.ext fun n ↦ ?_
  simp [DFinsupp.mapRange.addEquiv_apply, DFinsupp.mapRange_apply,
    bivariantClassSourceComponentCongr]

/-- **The composite, for left factors into equal connected components.** Composing with the
restriction of `h` to a connected component `Z_u` of `Z` respects replacing `u` by an equal index
and the left factor by a heterogeneously equal one. -/
theorem bivariantCompositeOfInvertible_heq_of_source_component
    {u₁ u₂ : _root_.ConnectedComponents Z} (hu : u₁ = u₂)
    (φ₁ : V ⟶ (Z.connectedComponentOpens u₁ : Scheme.{u})) [LocallyOfFiniteType φ₁]
    (φ₂ : V ⟶ (Z.connectedComponentOpens u₂ : Scheme.{u})) [LocallyOfFiniteType φ₂]
    (hφ : φ₁ ≍ φ₂) (hφ₁ : φ₁ ≫ ((Z.connectedComponentOpens u₁).ι ≫ sZ) = sV)
    (hφ₂ : φ₂ ≫ ((Z.connectedComponentOpens u₂).ι ≫ sZ) = sV) (p q : ℤ)
    (a₁ : BivariantClass C (gysinSystemOfInvertible C) sV ((Z.connectedComponentOpens u₁).ι ≫ sZ)
      φ₁ hφ₁ p)
    (a₂ : BivariantClass C (gysinSystemOfInvertible C) sV ((Z.connectedComponentOpens u₂).ι ≫ sZ)
      φ₂ hφ₂ p) (ha : a₁ ≍ a₂)
    (b₁ : BivariantClass C (gysinSystemOfInvertible C) ((Z.connectedComponentOpens u₁).ι ≫ sZ)
        ((W.connectedComponentOpens (h.continuous.connectedComponentsMap u₁)).ι ≫ sW)
        (h.resConnectedComponent u₁) (h.resConnectedComponent_comp_ι_comp hh u₁) q)
    (b₂ : BivariantClass C (gysinSystemOfInvertible C) ((Z.connectedComponentOpens u₂).ι ≫ sZ)
        ((W.connectedComponentOpens (h.continuous.connectedComponentsMap u₂)).ι ≫ sW)
        (h.resConnectedComponent u₂) (h.resConnectedComponent_comp_ι_comp hh u₂) q)
    (hb : b₁ ≍ b₂) :
    bivariantCompositeOfInvertible C sV _ _ φ₁ (h.resConnectedComponent u₁) hφ₁
        (h.resConnectedComponent_comp_ι_comp hh u₁) p q a₁ b₁ ≍
      bivariantCompositeOfInvertible C sV _ _ φ₂ (h.resConnectedComponent u₂) hφ₂
        (h.resConnectedComponent_comp_ι_comp hh u₂) p q a₂ b₂ := by
  subst hu
  obtain rfl := eq_of_heq hφ
  obtain rfl := eq_of_heq ha
  obtain rfl := eq_of_heq hb
  rfl

/-- **The composite, for right factors into equal connected components.** Composing a class `a`
with a class for a morphism into a connected component `W_j` of `W` respects replacing `j` by an
equal index and the right factor by a heterogeneously equal class for a heterogeneously equal
morphism. -/
theorem bivariantCompositeOfInvertible_heq_of_target_component {Y' : Scheme.{u}}
    (sY' : Y' ⟶ C.S) [LocallyOfFiniteType sY'] (φ : V ⟶ Y') [LocallyOfFiniteType φ]
    (hφ : φ ≫ sY' = sV) {j₁ j₂ : _root_.ConnectedComponents W} (hj : j₁ = j₂)
    (ψ₁ : Y' ⟶ (W.connectedComponentOpens j₁ : Scheme.{u})) [LocallyOfFiniteType ψ₁]
    (ψ₂ : Y' ⟶ (W.connectedComponentOpens j₂ : Scheme.{u})) [LocallyOfFiniteType ψ₂]
    (hψ : ψ₁ ≍ ψ₂) (hψ₁ : ψ₁ ≫ ((W.connectedComponentOpens j₁).ι ≫ sW) = sY')
    (hψ₂ : ψ₂ ≫ ((W.connectedComponentOpens j₂).ι ≫ sW) = sY') (p q : ℤ)
    (a : BivariantClass C (gysinSystemOfInvertible C) sV sY' φ hφ p)
    (b₁ : BivariantClass C (gysinSystemOfInvertible C) sY' ((W.connectedComponentOpens j₁).ι ≫ sW)
      ψ₁ hψ₁ q)
    (b₂ : BivariantClass C (gysinSystemOfInvertible C) sY' ((W.connectedComponentOpens j₂).ι ≫ sW)
      ψ₂ hψ₂ q) (hb : b₁ ≍ b₂) :
    bivariantCompositeOfInvertible C sV sY' _ φ ψ₁ hφ hψ₁ p q a b₁ ≍
      bivariantCompositeOfInvertible C sV sY' _ φ ψ₂ hφ hψ₂ p q a b₂ := by
  subst hj
  obtain rfl := eq_of_heq hψ
  obtain rfl := eq_of_heq hb
  rfl

end ComponentCongr

/-! ### Associativity on completions -/

section Assoc

variable (C : ChowSituation.{u}) {X Y Z W : Scheme.{u}} (sX : X ⟶ C.S) [LocallyOfFiniteType sX]
  (sY : Y ⟶ C.S) [LocallyOfFiniteType sY] (sZ : Z ⟶ C.S) [LocallyOfFiniteType sZ]
  (sW : W ⟶ C.S) [LocallyOfFiniteType sW] (f : X ⟶ Y) [LocallyOfFiniteType f]
  (g : Y ⟶ Z) [LocallyOfFiniteType g] (h : Z ⟶ W) [LocallyOfFiniteType h]
  (hf : f ≫ sY = sX) (hg : g ≫ sZ = sY) (hh : h ≫ sW = sZ)
  [IsLocallyNoetherian X] [IsLocallyNoetherian Y] [IsLocallyNoetherian Z] [IsLocallyNoetherian W]

/-- The identification of the groups of classes on a connected component `X_w` of `X` for the
equal morphisms `(f ≫ g) ≫ h` and `f ≫ (g ≫ h)`. -/
def completedAssocTransport (w : _root_.ConnectedComponents X) (n : ℤ) :
    BivariantClass C (gysinSystemOfInvertible C) ((X.connectedComponentOpens w).ι ≫ sX)
        ((W.connectedComponentOpens (((f ≫ g) ≫ h).continuous.connectedComponentsMap w)).ι ≫ sW)
        (((f ≫ g) ≫ h).resConnectedComponent w)
        (((f ≫ g) ≫ h).resConnectedComponent_comp_ι_comp
          (comp_comp_structureMorphism_eq (comp_comp_structureMorphism_eq hf hg) hh) w) n ≃+
      BivariantClass C (gysinSystemOfInvertible C) ((X.connectedComponentOpens w).ι ≫ sX)
        ((W.connectedComponentOpens ((f ≫ g ≫ h).continuous.connectedComponentsMap w)).ι ≫ sW)
        ((f ≫ g ≫ h).resConnectedComponent w)
        ((f ≫ g ≫ h).resConnectedComponent_comp_ι_comp
          (comp_comp_structureMorphism_eq hf (comp_comp_structureMorphism_eq hg hh)) w) n :=
  bivariantClassComponentCongr C (gysinSystemOfInvertible C)
    ((X.connectedComponentOpens w).ι ≫ sX) sW (by rw [Category.assoc]) _ _
    (congr_arg_heq (fun k : X ⟶ W ↦ k.resConnectedComponent w) (Category.assoc f g h)) _ _ n

omit [LocallyOfFiniteType sY] [LocallyOfFiniteType sZ] [IsLocallyNoetherian Y]
  [IsLocallyNoetherian Z] in
/-- The identification `Stacks.Chow.completedAssocTransport` changes nothing. -/
theorem completedAssocTransport_heq (w : _root_.ConnectedComponents X) (n : ℤ) (x) :
    completedAssocTransport C sX sY sZ sW f g h hf hg hh w n x ≍ x :=
  bivariantClassComponentCongr_heq C _ _ _ _ _ _ _ _ n x

/-- The homogeneous step of associativity on completions: for classes `x`, `y`, `z` on the
connected components `X_w`, `Y_{a(w)}` and `Z_{(f ≫ g)(w)}`, the two iterated composites, read
through the transports of the completed composition, agree. -/
theorem completedAssoc_homogeneous (w : _root_.ConnectedComponents X) (p q r : ℤ)
    (x : BivariantClass C (gysinSystemOfInvertible C) ((X.connectedComponentOpens w).ι ≫ sX)
      ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι ≫ sY)
      (f.resConnectedComponent w) (f.resConnectedComponent_comp_ι_comp hf w) p)
    (y : BivariantClass C (gysinSystemOfInvertible C)
      ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι ≫ sY)
      ((Z.connectedComponentOpens (g.continuous.connectedComponentsMap
        (f.continuous.connectedComponentsMap w))).ι ≫ sZ)
      (g.resConnectedComponent (f.continuous.connectedComponentsMap w))
      (g.resConnectedComponent_comp_ι_comp hg (f.continuous.connectedComponentsMap w)) q)
    (z : BivariantClass C (gysinSystemOfInvertible C)
      ((Z.connectedComponentOpens ((f ≫ g).continuous.connectedComponentsMap w)).ι ≫ sZ)
      ((W.connectedComponentOpens (h.continuous.connectedComponentsMap
        ((f ≫ g).continuous.connectedComponentsMap w))).ι ≫ sW)
      (h.resConnectedComponent ((f ≫ g).continuous.connectedComponentsMap w))
      (h.resConnectedComponent_comp_ι_comp hh ((f ≫ g).continuous.connectedComponentsMap w)) r) :
    completedAssocTransport C sX sY sZ sW f g h hf hg hh w (p + q + r)
        (completedBivariantCompositeTransport C (gysinSystemOfInvertible C) sX sZ sW (f ≫ g) h
          (comp_comp_structureMorphism_eq hf hg) hh w (p + q + r)
          (bivariantCompositeOfInvertible C _ _ _ _ _ _ _ (p + q) r
            (completedBivariantCompositeTransport C (gysinSystemOfInvertible C) sX sY sZ f g hf hg
              w (p + q) (bivariantCompositeOfInvertible C _ _ _ _ _ _ _ p q x y)) z)) ≍
      completedBivariantCompositeTransport C (gysinSystemOfInvertible C) sX sY sW f (g ≫ h) hf
        (comp_comp_structureMorphism_eq hg hh) w (p + (q + r))
        (bivariantCompositeOfInvertible C _ _ _ _ _ _ _ p (q + r) x
          (completedBivariantCompositeTransport C (gysinSystemOfInvertible C) sY sZ sW g h hg hh
            (f.continuous.connectedComponentsMap w) (q + r)
            (bivariantCompositeOfInvertible C _ _ _ _ _ _ _ q r y
              (bivariantClassSourceComponentCongr C sZ sW h hh
                (Scheme.Hom.connectedComponentsMap_comp f g w) r z)))) := by
  refine (completedAssocTransport_heq C sX sY sZ sW f g h hf hg hh w _ _).trans ?_
  refine (bivariantClassComponentCongr_heq C _ _ _ _ _ _ _ _ _ _).trans ?_
  refine HEq.trans ?_ (bivariantClassComponentCongr_heq C _ _ _ _ _ _ _ _ _ _).symm
  refine (bivariantCompositeOfInvertible_heq_of_source_component C _ sZ sW h hh
    (Scheme.Hom.connectedComponentsMap_comp f g w) _ _
    (Scheme.Hom.heq_resConnectedComponent_comp f g w) _ _ _ _ _ _
    (bivariantClassComponentCongr_heq C _ _ _ _ _ _ _ _ _ _) _ _
    (bivariantClassSourceComponentCongr_heq C sZ sW h hh
      (Scheme.Hom.connectedComponentsMap_comp f g w) r z).symm).trans ?_
  refine (bivariantCompositeOfInvertible_assoc C _ _ _ _ _ _ _ _ _ _ p q r x y _).trans ?_
  exact bivariantCompositeOfInvertible_heq_of_target_component C (sW := sW)
    (hj := (Scheme.Hom.connectedComponentsMap_comp g h _).symm)
    (hψ := (Scheme.Hom.heq_resConnectedComponent_comp g h _).symm) (a := x)
    (hb := (bivariantClassComponentCongr_heq C _ _ _ _ _ _ _ _ _ _).symm)

/-- **Associativity of the composition on completions.** For completed classes
`c ∈ A^*(X ⟶ Y)^∧`, `d ∈ A^*(Y ⟶ Z)^∧` and `e ∈ A^*(Z ⟶ W)^∧` (Stacks 0FE0),
`(c ∘ d) ∘ e = c ∘ (d ∘ e)` in `A^*(X ⟶ W)^∧`, at the Gysin system of the first Chern class rule.
The two sides are completed classes for `(f ≫ g) ≫ h` and `f ≫ (g ≫ h)`, whence the heterogeneous
equality. -/
theorem completedBivariantCompositeOfInvertible_assoc
    (c : completedBivariantGroup C (gysinSystemOfInvertible C) sX sY f hf)
    (d : completedBivariantGroup C (gysinSystemOfInvertible C) sY sZ g hg)
    (e : completedBivariantGroup C (gysinSystemOfInvertible C) sZ sW h hh) :
    completedBivariantCompositeOfInvertible C sX sZ sW (f ≫ g) h
        (comp_comp_structureMorphism_eq hf hg) hh
        (completedBivariantCompositeOfInvertible C sX sY sZ f g hf hg c d) e ≍
      completedBivariantCompositeOfInvertible C sX sY sW f (g ≫ h) hf
        (comp_comp_structureMorphism_eq hg hh) c
        (completedBivariantCompositeOfInvertible C sY sZ sW g h hg hh d e) := by
  refine completedBivariantGroup_heq_of_apply_heq C (Category.assoc f g h) _ _ fun w n ↦ ?_
  have hb : g.continuous.connectedComponentsMap (f.continuous.connectedComponentsMap w) =
      (f ≫ g).continuous.connectedComponentsMap w :=
    (Scheme.Hom.connectedComponentsMap_comp f g w).symm
  let Φ := completedAssocTransport C sX sY sZ sW f g h hf hg hh w
  suffices hΦ : DFinsupp.mapRange.addEquiv Φ
      (completedBivariantCompositeOfInvertible C sX sZ sW (f ≫ g) h
        (comp_comp_structureMorphism_eq hf hg) hh
        (completedBivariantCompositeOfInvertible C sX sY sZ f g hf hg c d) e w) =
      completedBivariantCompositeOfInvertible C sX sY sW f (g ≫ h) hf
        (comp_comp_structureMorphism_eq hg hh) c
        (completedBivariantCompositeOfInvertible C sY sZ sW g h hg hh d e) w by
    rw [← hΦ, DFinsupp.mapRange.addEquiv_apply, DFinsupp.mapRange_apply]
    exact (completedAssocTransport_heq C sX sY sZ sW f g h hf hg hh w n _).symm
  have key := directSumBilinear_assoc_of_mapRange
    (fun p q ↦ bivariantCompositeBilinear C (gysinSystemOfInvertible C)
      ((X.connectedComponentOpens w).ι ≫ sX)
      ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι ≫ sY)
      ((Z.connectedComponentOpens (g.continuous.connectedComponentsMap
        (f.continuous.connectedComponentsMap w))).ι ≫ sZ)
      (f.resConnectedComponent w) (g.resConnectedComponent (f.continuous.connectedComponentsMap w))
      (f.resConnectedComponent_comp_ι_comp hf w)
      (g.resConnectedComponent_comp_ι_comp hg (f.continuous.connectedComponentsMap w)) p q
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C))
    (completedBivariantCompositeTransport C (gysinSystemOfInvertible C) sX sY sZ f g hf hg w)
    (fun p q ↦ bivariantCompositeBilinear C (gysinSystemOfInvertible C)
      ((X.connectedComponentOpens w).ι ≫ sX)
      ((Z.connectedComponentOpens ((f ≫ g).continuous.connectedComponentsMap w)).ι ≫ sZ)
      ((W.connectedComponentOpens (h.continuous.connectedComponentsMap
        ((f ≫ g).continuous.connectedComponentsMap w))).ι ≫ sW)
      ((f ≫ g).resConnectedComponent w)
      (h.resConnectedComponent ((f ≫ g).continuous.connectedComponentsMap w))
      ((f ≫ g).resConnectedComponent_comp_ι_comp (comp_comp_structureMorphism_eq hf hg) w)
      (h.resConnectedComponent_comp_ι_comp hh ((f ≫ g).continuous.connectedComponentsMap w)) p q
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C))
    (completedBivariantCompositeTransport C (gysinSystemOfInvertible C) sX sZ sW (f ≫ g) h
      (comp_comp_structureMorphism_eq hf hg) hh w) Φ
    (fun q r ↦ bivariantCompositeBilinear C (gysinSystemOfInvertible C)
      ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι ≫ sY)
      ((Z.connectedComponentOpens (g.continuous.connectedComponentsMap
        (f.continuous.connectedComponentsMap w))).ι ≫ sZ)
      ((W.connectedComponentOpens (h.continuous.connectedComponentsMap
        (g.continuous.connectedComponentsMap (f.continuous.connectedComponentsMap w)))).ι ≫ sW)
      (g.resConnectedComponent (f.continuous.connectedComponentsMap w))
      (h.resConnectedComponent (g.continuous.connectedComponentsMap
        (f.continuous.connectedComponentsMap w)))
      (g.resConnectedComponent_comp_ι_comp hg (f.continuous.connectedComponentsMap w))
      (h.resConnectedComponent_comp_ι_comp hh (g.continuous.connectedComponentsMap
        (f.continuous.connectedComponentsMap w))) q r
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C))
    (completedBivariantCompositeTransport C (gysinSystemOfInvertible C) sY sZ sW g h hg hh
      (f.continuous.connectedComponentsMap w))
    (fun p t ↦ bivariantCompositeBilinear C (gysinSystemOfInvertible C)
      ((X.connectedComponentOpens w).ι ≫ sX)
      ((Y.connectedComponentOpens (f.continuous.connectedComponentsMap w)).ι ≫ sY)
      ((W.connectedComponentOpens ((g ≫ h).continuous.connectedComponentsMap
        (f.continuous.connectedComponentsMap w))).ι ≫ sW)
      (f.resConnectedComponent w) ((g ≫ h).resConnectedComponent
        (f.continuous.connectedComponentsMap w))
      (f.resConnectedComponent_comp_ι_comp hf w)
      ((g ≫ h).resConnectedComponent_comp_ι_comp (comp_comp_structureMorphism_eq hg hh)
        (f.continuous.connectedComponentsMap w)) p t
      (gysinSystemOfInvertible_isNaturalUnderBaseChangeIso C)
      (gysinSystemOfInvertible_isNaturalUnderPullbackCompPushforward C))
    (completedBivariantCompositeTransport C (gysinSystemOfInvertible C) sX sY sW f (g ≫ h) hf
      (comp_comp_structureMorphism_eq hg hh) w)
    (bivariantClassSourceComponentCongr C sZ sW h hh hb.symm) (c w)
    (d (f.continuous.connectedComponentsMap w))
    (e ((f ≫ g).continuous.connectedComponentsMap w))
    (e (g.continuous.connectedComponentsMap (f.continuous.connectedComponentsMap w)))
    (mapRange_bivariantClassSourceComponentCongr C sZ sW h hh e hb.symm)
  exact key fun p q r x y z ↦
    completedAssoc_homogeneous C sX sY sZ sW f g h hf hg hh w p q r x y z

end Assoc

end Stacks.Chow

end
