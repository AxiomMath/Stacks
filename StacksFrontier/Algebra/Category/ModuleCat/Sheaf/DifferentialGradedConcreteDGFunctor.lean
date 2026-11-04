module

public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedAxiomC
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedDerivedPullback
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.DifferentialGradedHomotopyCategoryTriangulated
public import StacksFrontier.CategoryTheory.DifferentialGraded.AddDGFunctorShift

/-!
# Functors of sheaf differential graded modules extended to homogeneous maps

Let `X` and `Y` be ringed sites and let `A` and `B` be sheaves of differential graded algebras on
them. A functor `G : Mod^dg(A, d) ⥤ Mod^dg(B, d)` which is extended to homogeneous maps — to
cochains commuting with the action, additively and compatibly with the differentials,
composition and identities — is a functor of differential graded categories in the additive
sense of `DGCategory.AddDGFunctor`, between the differential graded categories
`SheafOfModules.DifferentialGradedModule.dgCategoryData` of the two module categories.

## Main definitions

* `SheafOfModules.DifferentialGradedModule.ConcreteDGFunctor`: a functor of right differential
  graded modules together with its extension to homogeneous maps.
* `SheafOfModules.DifferentialGradedModule.ConcreteDGFunctor.dgFunctor`: the induced additive
  functor of differential graded categories.
* `SheafOfModules.DifferentialGradedModule.ConcreteDGFunctor.homotopyFunctor`: the induced
  functor of homotopy categories, and `homotopyFunctorIso` its identification with the functor
  of differential graded homotopy categories.

## Main results

* `SheafOfModules.DifferentialGradedModule.canonical_unitCoherent`: the canonical morphisms
  `x[n] ⟶ x` of the shift of sheaf differential graded modules are coherent.
* `SheafOfModules.DifferentialGradedModule.ConcreteDGFunctor.commShift` and
  `SheafOfModules.DifferentialGradedModule.ConcreteDGFunctor.isTriangulated`: **the induced
  functor of homotopy categories commutes with the translations and is triangulated**
  ([Stacks, Tag 0FQF]).

## References

* [Stacks Project, Tag 09L6](https://stacks.math.columbia.edu/tag/09L6)
* [Stacks Project, Tag 0FQF](https://stacks.math.columbia.edu/tag/0FQF)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits CochainComplex.HomComplex

universe u v v' w w'

namespace SheafOfModules.DifferentialGradedModule

variable {X Y : AlgebraicGeometry.RingedSite.{u, u, u}}
  {A : DifferentialGradedAlgebra.{u, v} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)}
  {B : DifferentialGradedAlgebra.{u, v'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)}

variable (A B) in
/-- **A functor of right differential graded modules extended to homogeneous maps**: a functor
`G` together with, for every cochain `c : M ⟶ N` of degree `k` commuting with the action, a
cochain `G c : G M ⟶ G N` of degree `k` commuting with the action, additively, compatibly with
the differentials of the hom complexes, with composition, and agreeing with `G` on morphisms. -/
structure ConcreteDGFunctor where
  /-- The functor. -/
  functor : DifferentialGradedModule.{u, v, w} A ⥤ DifferentialGradedModule.{u, v', w'} B
  /-- Its extension to homogeneous maps. -/
  mapCochain : ∀ {M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (c : Cochain M.complex N.complex k), IsActionLinear A c →
      Cochain (functor.obj M).complex (functor.obj N).complex k
  /-- The extension preserves linearity. -/
  isActionLinear_mapCochain : ∀ {M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (c : Cochain M.complex N.complex k) (hc : IsActionLinear A c),
      IsActionLinear B (mapCochain c hc)
  /-- The extension is additive. -/
  mapCochain_add : ∀ {M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (c c' : Cochain M.complex N.complex k) (hc : IsActionLinear A c)
    (hc' : IsActionLinear A c') (hcc' : IsActionLinear A (c + c')),
      mapCochain (c + c') hcc' = mapCochain c hc + mapCochain c' hc'
  /-- The extension commutes with the differentials of the hom complexes. -/
  mapCochain_delta : ∀ {M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (c : Cochain M.complex N.complex k) (hc : IsActionLinear A c)
    (hδ : IsActionLinear A (δ k (k + 1) c)),
      mapCochain (δ k (k + 1) c) hδ = δ k (k + 1) (mapCochain c hc)
  /-- The extension preserves composition. -/
  mapCochain_comp : ∀ {M N P : DifferentialGradedModule.{u, v, w} A} {k l m : ℤ}
    (c : Cochain M.complex N.complex k) (c' : Cochain N.complex P.complex l) (h : k + l = m)
    (hc : IsActionLinear A c) (hc' : IsActionLinear A c')
    (hcc' : IsActionLinear A (c.comp c' h)),
      mapCochain (c.comp c' h) hcc' = (mapCochain c hc).comp (mapCochain c' hc') h
  /-- The extension agrees with the functor on morphisms. -/
  mapCochain_ofHom : ∀ {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N),
    mapCochain (Cochain.ofHom f.toHomologicalComplex) (actionLinear_ofHom A f) =
      Cochain.ofHom (functor.map f).toHomologicalComplex

namespace ConcreteDGFunctor

variable (G : ConcreteDGFunctor.{u, v, v', w, w'} A B)

/-- The extension of `G` takes equal cochains to equal cochains, whatever the linearity proofs. -/
theorem mapCochain_congr {M N : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    {c c' : Cochain M.complex N.complex k} (h : c = c') (hc : IsActionLinear A c)
    (hc' : IsActionLinear A c') : G.mapCochain c hc = G.mapCochain c' hc' := by
  subst h; rfl

/-- The extension of `G` sends the identity cochain to the identity cochain. -/
theorem mapCochain_id (M : DifferentialGradedModule.{u, v, w} A) :
    G.mapCochain (Cochain.ofHom (𝟙 M.complex)) (actionLinear_id A M) =
      Cochain.ofHom (𝟙 (G.functor.obj M).complex) := by
  have h := G.mapCochain_ofHom (𝟙 M)
  rwa [G.functor.map_id] at h

/-- The homogeneous map of `B`-modules attached by `G` to a homogeneous morphism of the
differential graded category of `A`-modules. -/
noncomputable def homogeneousMap {x y : (dgCategoryData.{u, v, w} A).category.Obj} {k : ℤ}
    (f : (dgCategoryData.{u, v, w} A).category.Hom x y k) :
    HomogeneousMap B (G.functor.obj (moduleOf A (dgCategoryData A) x))
      (G.functor.obj (moduleOf A (dgCategoryData A) y)) k :=
  ⟨G.mapCochain (cochainOf A (dgCategoryData A) f) (homogeneousOf A _ f).2,
    G.isActionLinear_mapCochain _ _⟩

/-- The underlying cochain of the morphism attached to a homogeneous map is that map. -/
theorem underlying_moduleHomEquiv_symm {P Q : DifferentialGradedModule.{u, v', w'} B} {k : ℤ}
    (h : HomogeneousMap B P Q k) :
    underlyingCochain B (dgCategoryData B) ((moduleHomEquiv B (dgCategoryData B) P Q k).symm h) =
      h.val :=
  congrArg Subtype.val ((moduleHomEquiv B (dgCategoryData B) P Q k).apply_symm_apply h)

/-- The two readings of the underlying cochain of a homogeneous morphism agree. -/
theorem asCochain_eq_cochainOf {x y : (dgCategoryData.{u, v, w} A).category.Obj} {k : ℤ}
    (f : (dgCategoryData.{u, v, w} A).category.Hom x y k) :
    asCochain A f = cochainOf A (dgCategoryData A) f := rfl

/-- The underlying cochains of the identities and differentials of a differential graded category
of modules are the identity cochains and the differentials of the cochains. -/
private theorem cochainOf_id_and_d (D : DGCategoryData.{u, v, w} A) :
    (∀ x : D.category.Obj,
      cochainOf A D (D.category.id x) = Cochain.ofHom (𝟙 (moduleOf A D x).complex)) ∧
    ∀ {x y : D.category.Obj} {k : ℤ} (f : D.category.Hom x y k),
      cochainOf A D (D.category.d f) = δ k (k + 1) (cochainOf A D f) := by
  rcases D with ⟨C, ho, hh, _hadd, hd, hc, hi⟩
  rcases C with ⟨O, H, ac, mo, d, da, ds, dd, c, ca, cb, cs, ct, dl, ass, id, il, ir, di⟩
  dsimp only at ho
  subst O
  have he : H = HomogeneousMap A := by
    funext M N n
    exact hh M N n
  subst H
  exact ⟨fun x => eq_of_heq (hi x), fun {x y k} f => eq_of_heq (hd x y k f)⟩

/-- The underlying cochain of an identity morphism is the identity cochain. -/
theorem cochainOf_id' (x : (dgCategoryData.{u, v, w} A).category.Obj) :
    cochainOf A (dgCategoryData A) ((dgCategoryData.{u, v, w} A).category.id x) =
      Cochain.ofHom (𝟙 (moduleOf A (dgCategoryData A) x).complex) :=
  (cochainOf_id_and_d _).1 x

/-- The underlying cochain of the differential of a morphism is the differential of its cochain. -/
theorem cochainOf_d' {x y : (dgCategoryData.{u, v, w} A).category.Obj} {k : ℤ}
    (f : (dgCategoryData.{u, v, w} A).category.Hom x y k) :
    cochainOf A (dgCategoryData A) ((dgCategoryData.{u, v, w} A).category.d f) =
      δ k (k + 1) (cochainOf A (dgCategoryData A) f) :=
  (cochainOf_id_and_d _).2 f

/-- The underlying cochain of the differential of a morphism between modules. -/
theorem underlying_d' {P Q : DifferentialGradedModule.{u, v', w'} B} {k : ℤ}
    (f : (dgCategoryData.{u, v', w'} B).category.Hom (moduleObject B (dgCategoryData B) P)
      (moduleObject B (dgCategoryData B) Q) k) :
    underlyingCochain B (dgCategoryData B) ((dgCategoryData.{u, v', w'} B).category.d f) =
      δ k (k + 1) (underlyingCochain B (dgCategoryData B) f) :=
  eq_of_heq ((dgCategoryData B).differential P Q k f)

/-- The underlying cochain of the identity of a module. -/
theorem underlying_id' (P : DifferentialGradedModule.{u, v', w'} B) :
    underlyingCochain B (dgCategoryData B)
        ((dgCategoryData.{u, v', w'} B).category.id (moduleObject B (dgCategoryData B) P)) =
      Cochain.ofHom (𝟙 P.complex) :=
  eq_of_heq ((dgCategoryData B).identity P)

/-- **The additive functor of differential graded categories induced by `G`.** On an object it
is `G` of the corresponding module; on a homogeneous morphism it is the extension of `G` to the
underlying cochain. -/
noncomputable def dgFunctor :
    DGCategory.AddDGFunctor (dgCategoryData.{u, v, w} A).category
      (dgCategoryData.{u, v', w'} B).category where
  obj x := moduleObject B (dgCategoryData B) (G.functor.obj (moduleOf A (dgCategoryData A) x))
  map f := (moduleHomEquiv B (dgCategoryData B) _ _ _).symm (G.homogeneousMap f)
  map_add {x y n} f g := by
    apply underlyingCochain_injective B (dgCategoryData B)
    rw [underlyingCochain_add, underlying_moduleHomEquiv_symm, underlying_moduleHomEquiv_symm,
      underlying_moduleHomEquiv_symm]
    simp only [homogeneousMap]
    rw [← G.mapCochain_add _ _ (homogeneousOf A _ f).2 (homogeneousOf A _ g).2
      (actionLinear_add A _ _ (homogeneousOf A _ f).2 (homogeneousOf A _ g).2)]
    exact G.mapCochain_congr (cochainOf_add A _
      (Classical.choice (hasBinaryBiproducts A x x)) f g) _ _
  map_d {x y n} f := by
    apply underlyingCochain_injective B (dgCategoryData B)
    rw [underlying_d', underlying_moduleHomEquiv_symm, underlying_moduleHomEquiv_symm]
    simp only [homogeneousMap]
    rw [← G.mapCochain_delta _ (homogeneousOf A _ f).2
      (actionLinear_delta A _ (homogeneousOf A _ f).2)]
    exact G.mapCochain_congr (cochainOf_d' f) _ _
  map_comp {x y z m n k} h g f := by
    apply underlyingCochain_injective B (dgCategoryData B)
    rw [underlyingCochain_comp, underlying_moduleHomEquiv_symm, underlying_moduleHomEquiv_symm,
      underlying_moduleHomEquiv_symm]
    simp only [homogeneousMap]
    rw [← G.mapCochain_comp _ _ _ (homogeneousOf A _ f).2 (homogeneousOf A _ g).2
      (actionLinear_comp A _ _ _ (homogeneousOf A _ f).2 (homogeneousOf A _ g).2)]
    exact G.mapCochain_congr (cochainOf_comp A _ h g f) _ _
  map_id x := by
    apply underlyingCochain_injective B (dgCategoryData B)
    rw [underlying_id', underlying_moduleHomEquiv_symm]
    simp only [homogeneousMap]
    rw [← G.mapCochain_id]
    exact G.mapCochain_congr (cochainOf_id' x) _ _

end ConcreteDGFunctor

/-! ### The canonical shift of sheaf differential graded modules is coherent -/

section Canonical

/-- Two components of a cochain with equal targets agree heterogeneously. -/
theorem cochain_v_heq_of_eq_target
    {M N : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {k : ℤ}
    (c : Cochain M N k) {p q q' : ℤ} (hq : q = q') (h : p + k = q) (h' : p + k = q') :
    HEq (c.v p q h) (c.v p q' h') := by
  subst hq; rfl

/-- A morphism heterogeneously equal to an identity is an `eqToHom`. -/
theorem eq_eqToHom_of_heq_id {C : Type*} [Category C] {P Q : C} (hPQ : P = Q) (f : P ⟶ Q)
    (hf : HEq f (𝟙 P)) : f = eqToHom hPQ := by
  subst hPQ
  simpa using eq_of_heq hf

/-- A homogeneous morphism of the differential graded category of `A`-modules is determined,
heterogeneously, by the components of its underlying cochain. -/
theorem hom_heq_of_components {x y x' y' : (dgCategoryData.{u, v, w} A).category.Obj}
    {k k' : ℤ} (hx : x = x') (hy : y = y') (hk : k = k')
    (g : (dgCategoryData.{u, v, w} A).category.Hom x y k)
    (g' : (dgCategoryData.{u, v, w} A).category.Hom x' y' k')
    (h : ∀ (p q : ℤ) (h₁ : p + k = q) (h₂ : p + k' = q),
      HEq ((asCochain A g).v p q h₁) ((asCochain A g').v p q h₂)) : HEq g g' := by
  subst hx hy hk
  exact heq_of_eq (asCochain_injective (Cochain.ext _ _ fun p q hpq =>
    eq_of_heq (h p q hpq hpq)))

/-- The underlying cochain of an identity morphism. -/
theorem asCochain_id (x : (dgCategoryData.{u, v, w} A).category.Obj) :
    asCochain A ((dgCategoryData.{u, v, w} A).category.id x) =
      Cochain.ofHom (𝟙 (asModule A x).complex) :=
  ConcreteDGFunctor.cochainOf_id' x

/-- The underlying cochain of a composite is the composite of the cochains. -/
theorem asCochain_comp {x y z : (dgCategoryData.{u, v, w} A).category.Obj} {m n k : ℤ}
    (h : m + n = k) (g : (dgCategoryData.{u, v, w} A).category.Hom y z m)
    (f : (dgCategoryData.{u, v, w} A).category.Hom x y n) :
    asCochain A ((dgCategoryData.{u, v, w} A).category.comp h g f) =
      (asCochain A f).comp (asCochain A g) (by omega) :=
  cochainOf_comp A _ h g f

variable (A) in
/-- The identifications of the canonical axiom (B), on components, at an arbitrary source. -/
theorem canonical_toShift_v_heq (n k : ℤ) {x' : (dgCategoryData.{u, v, w} A).category.Obj}
    (N : DifferentialGradedModule.{u, v, w} A)
    (f : (dgCategoryData.{u, v, w} A).category.Hom x' (asObject A N) (k + n))
    (p q : ℤ) (h : p + k = q) :
    HEq ((asCochain A ((shiftAxiomB.{u, v, w} A).axiomB.toShift n x' (asObject A N) k f)).v p q h)
      ((asCochain A f).v p (q + n) (by omega)) := by
  obtain ⟨M', rfl⟩ : ∃ M', asObject A M' = x' := ⟨asModule A x', asObject_asModule A x'⟩
  exact (shiftAxiomB.{u, v, w} A).toShift_components n k M' N f p q h

variable (A) in
/-- **The components of the canonical morphism `x[n] ⟶ x` are identities.** -/
theorem canonical_unit_v_heq (n : ℤ) (x : (dgCategoryData.{u, v, w} A).category.Obj)
    (p q : ℤ) (h : p + (0 + n) = q) :
    HEq ((asCochain A ((shiftAxiomB.{u, v, w} A).axiomB.unit n x)).v p q h)
      (𝟙 ((asModule A (((shiftAxiomB.{u, v, w} A).axiomB.shiftFunctor n).obj x)).complex.X p)) := by
  obtain ⟨M, rfl⟩ : ∃ M, asObject A M = x := ⟨asModule A x, asObject_asModule A x⟩
  have e := canonical_toShift_v_heq A n 0 M ((shiftAxiomB.{u, v, w} A).axiomB.unit n
    (asObject A M)) p p (add_zero p)
  rw [DGCategory.ShiftAxiomB.toShift_unit, asCochain_id, Cochain.ofHom_v] at e
  exact (cochain_v_heq_of_eq_target _ (by omega) _ _).trans e.symm

variable (A) in
/-- The pieces of a canonically shifted object are the pieces of the object, in the shifted
degree. -/
theorem canonical_shift_X (n : ℤ) (y : (dgCategoryData.{u, v, w} A).category.Obj) (p : ℤ) :
    (asModule A (((shiftAxiomB.{u, v, w} A).axiomB.shiftFunctor n).obj y)).complex.X p =
      (asModule A y).complex.X (p + n) := by
  obtain ⟨N, rfl⟩ : ∃ N, asObject A N = y := ⟨asModule A y, asObject_asModule A y⟩
  rw [(shiftAxiomB.{u, v, w} A).shifted_complex n N, asModule_asObject]
  rfl

/-- Two `eqToHom` morphisms between correspondingly equal objects agree heterogeneously. -/
theorem eqToHom_heq_eqToHom {C : Type*} [Category C] {P P' Q Q' : C} (h : P = Q) (h' : P' = Q')
    (hP : P = P') (hQ : Q = Q') : HEq (eqToHom h) (eqToHom h') := by
  subst hP hQ; rfl

variable (A) in
/-- **The canonical morphisms of the canonical axiom (B) are coherent.** -/
theorem canonical_unitCoherent : (shiftAxiomB.{u, v, w} A).axiomB.UnitCoherent where
  zero x := by
    set S := (shiftAxiomB.{u, v, w} A).axiomB
    refine hom_heq_of_components (S.zero_obj x) rfl (by omega) _ _ fun p q h₁ h₂ => ?_
    obtain rfl : p = q := by omega
    refine (canonical_unit_v_heq A 0 x p p h₁).trans ?_
    rw [asCochain_id, Cochain.ofHom_v]
    rw [S.zero_obj x]
    rfl
  add a b x := by
    set S := (shiftAxiomB.{u, v, w} A).axiomB
    have hobj : (S.shiftFunctor (a + b)).obj x =
        (S.shiftFunctor b).obj ((S.shiftFunctor a).obj x) := by
      rw [add_comm a b]; exact S.add_obj b a x
    refine hom_heq_of_components hobj rfl rfl _ _ fun p q h₁ h₂ => ?_
    rw [asCochain_comp, Cochain.comp_v _ _ _ p (p + (0 + b)) q rfl (by omega)]
    have e₁ := canonical_unit_v_heq A b ((S.shiftFunctor a).obj x) p (p + (0 + b)) rfl
    have e₂ := canonical_unit_v_heq A a x (p + (0 + b)) q (by omega)
    have e₀ := canonical_unit_v_heq A (a + b) x p q h₁
    have hX₁₂ : (asModule A ((S.shiftFunctor b).obj ((S.shiftFunctor a).obj x))).complex.X p =
        (asModule A ((S.shiftFunctor a).obj x)).complex.X (p + (0 + b)) :=
      (canonical_shift_X A b _ p).trans (congrArg _ (by omega))
    have hX₂₃ : (asModule A ((S.shiftFunctor a).obj x)).complex.X (p + (0 + b)) =
        (asModule A x).complex.X q :=
      (canonical_shift_X A a x _).trans (congrArg _ (by omega))
    have hX₀₃ : (asModule A ((S.shiftFunctor (a + b)).obj x)).complex.X p =
        (asModule A x).complex.X q :=
      (canonical_shift_X A (a + b) x p).trans (congrArg _ (by omega))
    rw [eq_eqToHom_of_heq_id hX₀₃ _ e₀, eq_eqToHom_of_heq_id hX₁₂ _ e₁,
      eq_eqToHom_of_heq_id hX₂₃ _ e₂, eqToHom_trans]
    exact eqToHom_heq_eqToHom _ _ (congrArg (fun y => (asModule A y).complex.X p) hobj) rfl

end Canonical

/-! ### The induced functor on homotopy categories -/

namespace ConcreteDGFunctor

variable (G : ConcreteDGFunctor.{u, v, v', w, w'} A B)

/-- Cochains between equal complexes agree heterogeneously when their components do. -/
theorem cochain_heq_ext'
    {M N M' N' : CochainComplex (SheafOfModules.{w} (Stacks.SheafOfModules.Tensor.ringSheaf X.O)) ℤ}
    {k : ℤ}
    (hM : M = M') (hN : N = N') (c : Cochain M N k) (c' : Cochain M' N' k)
    (h : ∀ p q (hpq : p + k = q), HEq (c.v p q hpq) (c'.v p q hpq)) : HEq c c' := by
  subst hM hN
  exact heq_of_eq (Cochain.ext c c' fun p q hpq => eq_of_heq (h p q hpq))

/-- The underlying cochain of the homogeneous morphism of a morphism of modules is the cochain of
that morphism. -/
theorem cochainOf_homogeneousOfHom_heq {M N : DifferentialGradedModule.{u, v, w} A} (f : M ⟶ N) :
    HEq (cochainOf A (dgCategoryData.{u, v, w} A)
        (homogeneousOfHom A (dgCategoryData.{u, v, w} A) f))
      (Cochain.ofHom f.toHomologicalComplex) := by
  rw [← homogeneousOfHom_underlying A (dgCategoryData.{u, v, w} A) f]
  exact cochain_heq_ext' (congrArg DifferentialGradedModule.complex (asModule_asObject M))
    (congrArg DifferentialGradedModule.complex (asModule_asObject N)) _ _
    fun p q hpq => asCochain_v_heq _ p q hpq

/-- The extension of `G` respects heterogeneous equality of cochains. -/
theorem mapCochain_heq {M N M' N' : DifferentialGradedModule.{u, v, w} A} {k : ℤ}
    (hM : M = M') (hN : N = N') (c : Cochain M.complex N.complex k)
    (c' : Cochain M'.complex N'.complex k) (h : HEq c c') (hc : IsActionLinear A c)
    (hc' : IsActionLinear A c') : HEq (G.mapCochain c hc) (G.mapCochain c' hc') := by
  subst hM hN
  obtain rfl := eq_of_heq h
  rfl

/-- The morphism attached to a homogeneous map respects heterogeneous equality. -/
theorem moduleHomEquiv_symm_heq {P Q P' Q' : DifferentialGradedModule.{u, v', w'} B} {k : ℤ}
    (hP : P = P') (hQ : Q = Q') (h : HomogeneousMap B P Q k) (h' : HomogeneousMap B P' Q' k)
    (hh : HEq h.val h'.val) :
    HEq ((moduleHomEquiv B (dgCategoryData.{u, v', w'} B) P Q k).symm h)
      ((moduleHomEquiv B (dgCategoryData.{u, v', w'} B) P' Q' k).symm h') := by
  subst hP hQ
  obtain rfl : h = h' := Subtype.ext (eq_of_heq hh)
  rfl

/-- **The functor of differential graded categories sends the cocycle of a morphism to the
cocycle of its image.** -/
theorem dgFunctor_map_homogeneousOfHom {M N : DifferentialGradedModule.{u, v, w} A}
    (f : M ⟶ N) :
    HEq (G.dgFunctor.map (homogeneousOfHom A (dgCategoryData.{u, v, w} A) f))
      (homogeneousOfHom B (dgCategoryData.{u, v', w'} B) (G.functor.map f)) := by
  refine moduleHomEquiv_symm_heq (congrArg G.functor.obj (asModule_asObject M))
    (congrArg G.functor.obj (asModule_asObject N)) _ _ ?_
  refine (mapCochain_heq G (asModule_asObject M) (asModule_asObject N) _ _
    (cochainOf_homogeneousOfHom_heq f) _ (actionLinear_ofHom A f)).trans ?_
  rw [G.mapCochain_ofHom]

/-- **A functor extended to homogeneous maps carries homotopic morphisms to homotopic
morphisms.** -/
theorem preservesHomotopic : PreservesHomotopic G.functor := by
  intro M N f g h
  have hA := (cocycleOfHom_homotopic_iff A (dgCategoryData.{u, v, w} A)
    (Classical.choice (hasBinaryBiproducts A _ _)) f g).2 h
  have hK : (Quotient.mk _
      (G.dgFunctor.mapCocycle (cocycleOfHom A (dgCategoryData.{u, v, w} A) f)) :
      (dgCategoryData.{u, v', w'} B).category.HomotopyClass _ _) =
      Quotient.mk _ (G.dgFunctor.mapCocycle (cocycleOfHom A (dgCategoryData.{u, v, w} A) g)) :=
    congrArg G.dgFunctor.mapHomotopyClass (Quotient.sound hA)
  refine (cocycleOfHom_homotopic_iff B (dgCategoryData.{u, v', w'} B)
    (Classical.choice (hasBinaryBiproducts B _ _)) (G.functor.map f) (G.functor.map g)).1 ?_
  have hx : G.dgFunctor.obj (asObject A M) =
      moduleObject B (dgCategoryData.{u, v', w'} B) (G.functor.obj M) :=
    congrArg (moduleObject B (dgCategoryData.{u, v', w'} B))
      (congrArg G.functor.obj (asModule_asObject M))
  have hy : G.dgFunctor.obj (asObject A N) =
      moduleObject B (dgCategoryData.{u, v', w'} B) (G.functor.obj N) :=
    congrArg (moduleObject B (dgCategoryData.{u, v', w'} B))
      (congrArg G.functor.obj (asModule_asObject N))
  have key : ∀ (x y : (dgCategoryData.{u, v', w'} B).category.Obj)
      (hx' : x = moduleObject B (dgCategoryData.{u, v', w'} B) (G.functor.obj M))
      (hy' : y = moduleObject B (dgCategoryData.{u, v', w'} B) (G.functor.obj N))
      (a b : (dgCategoryData.{u, v', w'} B).category.Cocycle x y)
      (a' b' : (dgCategoryData.{u, v', w'} B).category.Cocycle
        (moduleObject B (dgCategoryData.{u, v', w'} B) (G.functor.obj M))
        (moduleObject B (dgCategoryData.{u, v', w'} B) (G.functor.obj N))),
      HEq a.1 a'.1 → HEq b.1 b'.1 →
      Quotient.mk ((dgCategoryData.{u, v', w'} B).category.homotopySetoid x y) a = Quotient.mk _ b →
      (dgCategoryData.{u, v', w'} B).category.Homotopic a' b' := by
    intro x y hx' hy' a b a' b' ha hb hab
    subst hx' hy'
    obtain rfl : a = a' := Subtype.ext (eq_of_heq ha)
    obtain rfl : b = b' := Subtype.ext (eq_of_heq hb)
    exact Quotient.exact hab
  exact key _ _ hx hy _ _ _ _ (dgFunctor_map_homogeneousOfHom G f)
    (dgFunctor_map_homogeneousOfHom G g) hK

/-- Heterogeneously equal morphisms are conjugate by `eqToHom`. -/
theorem comp_eqToHom_eq_of_heq {C : Type*} [Category C] {P Q P' Q' : C} (m : P ⟶ Q)
    (m' : P' ⟶ Q') (hP : P = P') (hQ : Q = Q') (h : HEq m m') :
    m ≫ eqToHom hQ = eqToHom hP ≫ m' := by
  subst hP hQ
  simp [eq_of_heq h]

/-- The functor of homotopy categories induced by `G`. -/
noncomputable def homotopyFunctor : HomotopyCategory.{u, v, w} A ⥤ HomotopyCategory.{u, v', w'} B :=
  HomotopyCategory.descend G.functor G.preservesHomotopic

/-- The induced functor of homotopy categories factors `G` through the two quotient functors. -/
theorem quotient_comp_homotopyFunctor :
    HomotopyCategory.quotient A ⋙ G.homotopyFunctor = G.functor ⋙ HomotopyCategory.quotient B :=
  HomotopyCategory.quotient_comp_descend _ _

/-- The objects of the two composites of `homotopyFunctorIso` agree. -/
theorem homotopyFunctorIso_obj (Z : HomotopyCategory.{u, v, w} A) :
    (G.homotopyFunctor ⋙ homotopyCategoryToDG.{u, v', w'} B).obj Z =
      (homotopyCategoryToDG.{u, v, w} A ⋙ G.dgFunctor.onK).obj Z :=
  congrArg (moduleObject B (dgCategoryData.{u, v', w'} B))
    (congrArg G.functor.obj (asModule_asObject Z.as).symm)

/-- **The functor induced by `G` on the homotopy categories is the one induced by its
differential graded extension**, through the identifications of the homotopy categories with
those of the differential graded categories. -/
noncomputable def homotopyFunctorIso :
    G.homotopyFunctor ⋙ homotopyCategoryToDG.{u, v', w'} B ≅
      homotopyCategoryToDG.{u, v, w} A ⋙ G.dgFunctor.onK :=
  NatIso.ofComponents (fun Z => eqToIso (G.homotopyFunctorIso_obj Z)) (by
    intro Z Z' f
    obtain ⟨f, rfl⟩ := (HomotopyCategory.quotient A).map_surjective f
    refine comp_eqToHom_eq_of_heq _ _ (G.homotopyFunctorIso_obj _) (G.homotopyFunctorIso_obj _) ?_
    exact (DGCategory.homotopyClass_heq _ (G.homotopyFunctorIso_obj Z).symm
      (G.homotopyFunctorIso_obj Z').symm (dgFunctor_map_homogeneousOfHom G f)).symm)

variable (A) in
/-- The chosen cone situation of the differential graded category of modules has strict
translations. -/
theorem dgConeSituation_isStrictKShift :
    (dgConeSituation.{u, v, w} A).shift.IsStrictKShift := by
  rw [dgConeSituation_shift]
  exact isStrictKShift_shiftAxiomB A

variable (A) in
/-- The chosen cone situation of the differential graded category of modules has coherent
canonical morphisms. -/
theorem dgConeSituation_unitCoherent :
    (dgConeSituation.{u, v, w} A).shift.UnitCoherent := by
  rw [dgConeSituation_shift]
  exact canonical_unitCoherent A

/-- The functor of differential graded homotopy categories induced by `G` commutes with the
translations. -/
@[instance_reducible]
noncomputable instance dgFunctor_onK_commShift : G.dgFunctor.onK.CommShift ℤ :=
  G.dgFunctor.commShift (dgConeSituation A).shift (dgConeSituation B).shift
    (dgConeSituation_isStrictKShift A) (dgConeSituation_isStrictKShift B)
    (dgConeSituation_unitCoherent A) (dgConeSituation_unitCoherent B)

/-- The functor of differential graded homotopy categories induced by `G` is triangulated. -/
instance dgFunctor_onK_isTriangulated : G.dgFunctor.onK.IsTriangulated :=
  G.dgFunctor.isTriangulated (dgConeSituation A) (dgConeSituation B)
    (dgConeSituation_isStrictKShift A) (dgConeSituation_isStrictKShift B)
    (dgConeSituation_unitCoherent A) (dgConeSituation_unitCoherent B)

/-- **The functor of homotopy categories induced by `G` commutes with the translations.** -/
@[instance_reducible]
noncomputable instance commShift : G.homotopyFunctor.CommShift ℤ :=
  Functor.CommShift.ofComp G.homotopyFunctorIso ℤ

/-- The identification `homotopyFunctorIso` commutes with the translations. -/
instance homotopyFunctorIso_commShift : NatTrans.CommShift G.homotopyFunctorIso.hom ℤ :=
  Functor.CommShift.ofComp_compatibility G.homotopyFunctorIso ℤ

/-- **The functor of homotopy categories induced by `G` is an exact functor of triangulated
categories.** -/
instance isTriangulated : G.homotopyFunctor.IsTriangulated := by
  let _ : (homotopyCategoryToDG.{u, v', w'} B).IsTriangulated := ⟨fun _ h => h⟩
  let _ : (homotopyCategoryToDG.{u, v, w} A).IsTriangulated := ⟨fun _ h => h⟩
  exact (Functor.isTriangulated_iff_comp_right G.homotopyFunctorIso).2 inferInstance

end ConcreteDGFunctor

end SheafOfModules.DifferentialGradedModule
