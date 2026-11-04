module

public import Mathlib.Algebra.Homology.QuasiIso
public import Mathlib.Algebra.Homology.ShortComplex.ModuleCat
public import Mathlib.Algebra.Category.ModuleCat.Abelian

/-!
# Quasi-isomorphisms of complexes concentrated in two degrees

A morphism of complexes which vanish outside two degrees `i₀` and `i₁` is a quasi-isomorphism
exactly when it is one in those two degrees, since the homology of a complex vanishes wherever
the complex does. For complexes of modules concentrated in degrees `-1` and `0` the two
remaining conditions are elementary: the map must be bijective on the kernel of the single
differential and on its cokernel.

## Main results

* `HomologicalComplex.quasiIsoAt_of_isZero_X`: a morphism is a quasi-isomorphism in a degree
  where both complexes vanish.
* `HomologicalComplex.quasiIso_iff_of_isZero_X`: for complexes vanishing outside two degrees,
  being a quasi-isomorphism is being one in those two degrees.
* `HomologicalComplex.isIso_homologyMap_of_isIso_cyclesMap` and
  `HomologicalComplex.isIso_homologyMap_of_isIso_opcyclesMap`: in a degree with no incoming,
  resp. no outgoing, differential, homology is cycles, resp. opcycles.
* `HomologicalComplex.isIso_cyclesMap_of_isIso_kernelMap` and
  `HomologicalComplex.isIso_opcyclesMap_of_isIso_cokernelMap`: in an abelian category the map of
  cycles is the map of kernels of the differentials, and the map of opcycles the map of their
  cokernels.
* `CochainComplex.quasiIso_of_isZero_X_of_isIso_kernel_cokernel`: in an abelian category, a
  morphism of complexes concentrated in degrees `-1` and `0` is a quasi-isomorphism as soon as
  the maps it induces on the kernel and on the cokernel of the differential are isomorphisms.
* `HomologicalComplex.isIso_cyclesMap_of_bijective` and
  `HomologicalComplex.isIso_opcyclesMap_of_bijective`: for complexes of modules, the maps of
  cycles and of opcycles are isomorphisms as soon as they are bijective in elementary terms.
* `CochainComplex.quasiIso_of_isZero_X_of_bijective`: a morphism of complexes of modules
  concentrated in degrees `-1` and `0` is a quasi-isomorphism as soon as it is bijective on the
  kernel and on the cokernel of the differential.
* `CochainComplex.quasiIso_of_isZero_X_of_eqToHom`: the same criterion for a differential and
  two components presented as conjugates by equalities of the four nonzero terms.
* `CochainComplex.eq_zero_of_d_eq_zero_of_addEquiv`,
  `CochainComplex.exists_of_d_eq_zero_of_addEquiv`, `CochainComplex.exists_d_eq_of_addEquiv`
  and `CochainComplex.exists_add_d_eq_of_addEquiv`: the four elementary conditions transported
  along additive identifications of the four terms.
* `CategoryTheory.Functor.map_eqToHom_comp_comp_eqToHom`: a functor carries a conjugate by
  `eqToHom` to the conjugate by the `eqToHom` of the images.

## Implementation notes

The elementary conditions are stated as four implications rather than as bijectivity of two
maps between subquotients, so that no `Submodule` plumbing appears in the statement and a
caller can discharge them by hand.

The transport of those four conditions along additive identifications is kept separate from
`CochainComplex.quasiIso_of_isZero_X_of_eqToHom`, which speaks only of morphisms: a caller
whose terms are large sheaf-theoretic ones would otherwise have to form composite `AddEquiv`s
and compare their coercions, which is where the defeq checks become unmanageable. Each of the
four transport lemmas takes exactly one identification per term and none of them composed.

For a complex `K` of modules the identifications of `K.cycles i` with a kernel and of
`K.opcycles i` with a quotient are `CategoryTheory.ShortComplex.moduleCatCyclesIso` and
`CategoryTheory.ShortComplex.moduleCat_pOpcycles_eq_zero_iff`, applied to `K.sc i`. They are
used through proof terms rather than `rw`: `K.cycles i` is `(K.sc i).cycles` by definition but
not syntactically, and rewriting across that unfolding produces ill-typed motives.
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe v u

namespace CategoryTheory.Functor

/-- A functor carries a conjugate `eqToHom h₁ ≫ g ≫ eqToHom h₀.symm` of a morphism by two
equalities of objects to the conjugate of its image by the corresponding equalities of
images. -/
theorem map_eqToHom_comp_comp_eqToHom {C : Type*} [Category* C] {D : Type*} [Category* D]
    (F : C ⥤ D) {M M' N N' : C} (h₁ : M = M') (g : M' ⟶ N') (h₀ : N = N') :
    F.map (eqToHom h₁ ≫ g ≫ eqToHom h₀.symm) =
      eqToHom (congrArg F.obj h₁) ≫ F.map g ≫ eqToHom (congrArg F.obj h₀).symm := by
  subst h₁
  subst h₀
  simp

end CategoryTheory.Functor

namespace CategoryTheory.Limits

variable {C : Type*} [Category* C] [Abelian C]

/-- **The map of kernels is unchanged by rewriting the four objects of the square.**  A square
whose four morphisms are the conjugates by equalities of objects of the morphisms of another
square induces the same map on kernels, so one is an isomorphism exactly when the other is. -/
theorem isIso_kernel_map_of_eqToHom {M M' N N' P P' Q Q' : C}
    (e₁ : M = M') (e₀ : N = N') (g₁ : P = P') (g₀ : Q = Q')
    {dK : M' ⟶ N'} {dL : P' ⟶ Q'} {pc : M' ⟶ P'} {pt : N' ⟶ Q'}
    {dK₀ : M ⟶ N} {dL₀ : P ⟶ Q} {pc₀ : M ⟶ P} {pt₀ : N ⟶ Q}
    (hdK : dK₀ = eqToHom e₁ ≫ dK ≫ eqToHom e₀.symm)
    (hdL : dL₀ = eqToHom g₁ ≫ dL ≫ eqToHom g₀.symm)
    (hpc : pc₀ = eqToHom e₁ ≫ pc ≫ eqToHom g₁.symm)
    (hpt : pt₀ = eqToHom e₀ ≫ pt ≫ eqToHom g₀.symm)
    (w₀ : dK₀ ≫ pt₀ = pc₀ ≫ dL₀) (w : dK ≫ pt = pc ≫ dL)
    (h : IsIso (kernel.map dK dL pc pt w)) :
    IsIso (kernel.map dK₀ dL₀ pc₀ pt₀ w₀) := by
  subst e₁ e₀ g₁ g₀
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hdK hdL hpc hpt
  subst hdK hdL hpc hpt
  exact h

/-- **The map of cokernels is unchanged by rewriting the four objects of the square.**  The
cokernel companion of `CategoryTheory.Limits.isIso_kernel_map_of_eqToHom`. -/
theorem isIso_cokernel_map_of_eqToHom {M M' N N' P P' Q Q' : C}
    (e₁ : M = M') (e₀ : N = N') (g₁ : P = P') (g₀ : Q = Q')
    {dK : M' ⟶ N'} {dL : P' ⟶ Q'} {pc : M' ⟶ P'} {pt : N' ⟶ Q'}
    {dK₀ : M ⟶ N} {dL₀ : P ⟶ Q} {pc₀ : M ⟶ P} {pt₀ : N ⟶ Q}
    (hdK : dK₀ = eqToHom e₁ ≫ dK ≫ eqToHom e₀.symm)
    (hdL : dL₀ = eqToHom g₁ ≫ dL ≫ eqToHom g₀.symm)
    (hpc : pc₀ = eqToHom e₁ ≫ pc ≫ eqToHom g₁.symm)
    (hpt : pt₀ = eqToHom e₀ ≫ pt ≫ eqToHom g₀.symm)
    (w₀ : dK₀ ≫ pt₀ = pc₀ ≫ dL₀) (w : dK ≫ pt = pc ≫ dL)
    (h : IsIso (cokernel.map dK dL pc pt w)) :
    IsIso (cokernel.map dK₀ dL₀ pc₀ pt₀ w₀) := by
  subst e₁ e₀ g₁ g₀
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hdK hdL hpc hpt
  subst hdK hdL hpc hpt
  exact h

end CategoryTheory.Limits

namespace HomologicalComplex

section Abelian

variable {C : Type*} [Category* C] [Abelian C] {ι : Type*} {c : ComplexShape ι}

/-- A complex is exact in a degree in which it vanishes. -/
theorem exactAt_of_isZero_X (K : HomologicalComplex C c) (i : ι) (h : IsZero (K.X i)) :
    K.ExactAt i := by
  rw [HomologicalComplex.exactAt_iff, ShortComplex.exact_iff_isZero_homology]
  exact ShortComplex.isZero_homology_of_isZero_X₂ _ h

variable {K L : HomologicalComplex C c}

/-- A morphism of complexes is a quasi-isomorphism in a degree in which both complexes
vanish. -/
theorem quasiIsoAt_of_isZero_X (φ : K ⟶ L) (i : ι) (hK : IsZero (K.X i)) (hL : IsZero (L.X i)) :
    QuasiIsoAt φ i := by
  rw [quasiIsoAt_iff_exactAt φ i (exactAt_of_isZero_X K i hK)]
  exact exactAt_of_isZero_X L i hL

/-- A morphism of complexes which vanish outside the two degrees `i₀` and `i₁` is a
quasi-isomorphism exactly when it is a quasi-isomorphism in those two degrees. -/
theorem quasiIso_iff_of_isZero_X (φ : K ⟶ L) (i₀ i₁ : ι)
    (hK : ∀ i, i ≠ i₀ → i ≠ i₁ → IsZero (K.X i))
    (hL : ∀ i, i ≠ i₀ → i ≠ i₁ → IsZero (L.X i)) :
    QuasiIso φ ↔ QuasiIsoAt φ i₀ ∧ QuasiIsoAt φ i₁ := by
  refine ⟨fun h => ⟨h.quasiIsoAt i₀, h.quasiIsoAt i₁⟩, fun h => ⟨fun i => ?_⟩⟩
  by_cases e₀ : i = i₀
  · exact e₀ ▸ h.1
  by_cases e₁ : i = i₁
  · exact e₁ ▸ h.2
  exact quasiIsoAt_of_isZero_X φ i (hK i e₀ e₁) (hL i e₀ e₁)

/-- In a degree with no incoming differential, homology is cycles: if the map of cycles in
degree `i` is an isomorphism, so is the map of homology. -/
theorem isIso_homologyMap_of_isIso_cyclesMap (φ : K ⟶ L) (i j : ι) (hj : c.prev i = j)
    (hK : K.d j i = 0) (hL : L.d j i = 0) (h : IsIso (cyclesMap φ i)) :
    IsIso (homologyMap φ i) := by
  have h₁ := K.isIso_homologyπ j i hj hK
  have h₂ := L.isIso_homologyπ j i hj hL
  have e : homologyMap φ i = inv (K.homologyπ i) ≫ cyclesMap φ i ≫ L.homologyπ i := by
    rw [← homologyπ_naturality, IsIso.inv_hom_id_assoc]
  rw [e]
  infer_instance

/-- In a degree with no outgoing differential, homology is opcycles: if the map of opcycles in
degree `i` is an isomorphism, so is the map of homology. -/
theorem isIso_homologyMap_of_isIso_opcyclesMap (φ : K ⟶ L) (i j : ι) (hj : c.next i = j)
    (hK : K.d i j = 0) (hL : L.d i j = 0) (h : IsIso (opcyclesMap φ i)) :
    IsIso (homologyMap φ i) := by
  have h₁ := K.isIso_homologyι i j hj hK
  have h₂ := L.isIso_homologyι i j hj hL
  have e : homologyMap φ i = K.homologyι i ≫ opcyclesMap φ i ≫ inv (L.homologyι i) := by
    rw [← homologyι_naturality_assoc, IsIso.hom_inv_id, Category.comp_id]
  rw [e]
  infer_instance

/-- The cycles of a complex in a degree are the kernel of the differential out of it: the
comparison map `K.cycles i ⟶ kernel (K.d i j)` determined by `K.iCycles i` is an
isomorphism. -/
theorem isIso_kernel_lift_iCycles (K : HomologicalComplex C c) (i j : ι) (hj : c.next i = j) :
    IsIso (kernel.lift (K.d i j) (K.iCycles i) (K.iCycles_d i j)) := by
  refine ⟨K.liftCycles (kernel.ι (K.d i j)) j hj (kernel.condition (K.d i j)), ?_, ?_⟩
  · rw [← cancel_mono (K.iCycles i), Category.assoc, Category.id_comp,
      K.liftCycles_i (kernel.ι (K.d i j)) j hj (kernel.condition (K.d i j)), kernel.lift_ι]
  · rw [← cancel_mono (kernel.ι (K.d i j)), Category.assoc, Category.id_comp, kernel.lift_ι,
      K.liftCycles_i (kernel.ι (K.d i j)) j hj (kernel.condition (K.d i j))]

/-- The opcycles of a complex in a degree are the cokernel of the differential into it: the
comparison map `K.opcycles j ⟶ cokernel (K.d i j)` determined by `K.pOpcycles j` is an
isomorphism. -/
theorem isIso_descOpcycles_pOpcycles (K : HomologicalComplex C c) (i j : ι)
    (hi : c.prev j = i) :
    IsIso (K.descOpcycles (cokernel.π (K.d i j)) i hi (cokernel.condition (K.d i j))) := by
  refine ⟨cokernel.desc (K.d i j) (K.pOpcycles j) (K.d_pOpcycles i j), ?_, ?_⟩
  · rw [← cancel_epi (K.pOpcycles j), ← Category.assoc, Category.comp_id,
      K.p_descOpcycles (cokernel.π (K.d i j)) i hi (cokernel.condition (K.d i j)),
      cokernel.π_desc]
  · rw [← cancel_epi (cokernel.π (K.d i j)), ← Category.assoc, Category.comp_id,
      cokernel.π_desc,
      K.p_descOpcycles (cokernel.π (K.d i j)) i hi (cokernel.condition (K.d i j))]

/-- **The map of cycles is the map of kernels.**  If the map induced on the kernels of the two
differentials out of a degree is an isomorphism, then so is the map of cycles in that degree:
the cycles are the kernel of the differential, compatibly with the morphism of complexes. -/
theorem isIso_cyclesMap_of_isIso_kernelMap (φ : K ⟶ L) (i j : ι) (hj : c.next i = j)
    (h : IsIso (kernel.map (K.d i j) (L.d i j) (φ.f i) (φ.f j) (φ.comm i j).symm)) :
    IsIso (cyclesMap φ i) := by
  have := isIso_kernel_lift_iCycles K i j hj
  have := isIso_kernel_lift_iCycles L i j hj
  have hsq : cyclesMap φ i ≫ kernel.lift (L.d i j) (L.iCycles i) (L.iCycles_d i j) =
      kernel.lift (K.d i j) (K.iCycles i) (K.iCycles_d i j) ≫
        kernel.map (K.d i j) (L.d i j) (φ.f i) (φ.f j) (φ.comm i j).symm := by
    rw [← cancel_mono (kernel.ι (L.d i j))]
    simp [cyclesMap_i]
  have : IsIso (cyclesMap φ i ≫
      kernel.lift (L.d i j) (L.iCycles i) (L.iCycles_d i j)) := by
    rw [hsq]; infer_instance
  exact IsIso.of_isIso_comp_right _ (kernel.lift (L.d i j) (L.iCycles i) (L.iCycles_d i j))

/-- **The map of opcycles is the map of cokernels.**  If the map induced on the cokernels of the
two differentials into a degree is an isomorphism, then so is the map of opcycles in that
degree: the opcycles are the cokernel of the differential, compatibly with the morphism of
complexes. -/
theorem isIso_opcyclesMap_of_isIso_cokernelMap (φ : K ⟶ L) (i j : ι) (hi : c.prev j = i)
    (h : IsIso (cokernel.map (K.d i j) (L.d i j) (φ.f i) (φ.f j) (φ.comm i j).symm)) :
    IsIso (opcyclesMap φ j) := by
  have := isIso_descOpcycles_pOpcycles K i j hi
  have := isIso_descOpcycles_pOpcycles L i j hi
  have hsq : opcyclesMap φ j ≫
        L.descOpcycles (cokernel.π (L.d i j)) i hi (cokernel.condition (L.d i j)) =
      K.descOpcycles (cokernel.π (K.d i j)) i hi (cokernel.condition (K.d i j)) ≫
        cokernel.map (K.d i j) (L.d i j) (φ.f i) (φ.f j) (φ.comm i j).symm := by
    rw [← cancel_epi (K.pOpcycles j)]
    simp
  have : IsIso (opcyclesMap φ j ≫
      L.descOpcycles (cokernel.π (L.d i j)) i hi (cokernel.condition (L.d i j))) := by
    rw [hsq]; infer_instance
  exact IsIso.of_isIso_comp_right _
    (L.descOpcycles (cokernel.π (L.d i j)) i hi (cokernel.condition (L.d i j)))

end Abelian

section ModuleCat

variable {R : Type u} [Ring R] {ι : Type*} {c : ComplexShape ι}

/-- Every element of a complex of modules killed by the differential out of its degree is the
image of a cycle. -/
theorem exists_iCycles_eq (K : HomologicalComplex (ModuleCat.{v} R) c) (i : ι) (x : K.X i)
    (hx : K.d i (c.next i) x = 0) : ∃ a : K.cycles i, K.iCycles i a = x :=
  ⟨_, ShortComplex.moduleCatCyclesIso_inv_iCycles_apply (K.sc i) ⟨x, hx⟩⟩

/-- An element of a complex of modules whose class in the opcycles of its degree vanishes is in
the image of the differential into that degree. -/
theorem exists_d_eq_of_pOpcycles_eq_zero (K : HomologicalComplex (ModuleCat.{v} R) c) (i : ι)
    (x : K.X i) (hx : K.pOpcycles i x = 0) : ∃ y : K.X (c.prev i), K.d (c.prev i) i y = x :=
  ((ShortComplex.moduleCat_pOpcycles_eq_zero_iff (K.sc i) x).mp hx).imp fun _ h => h

variable {K L : HomologicalComplex (ModuleCat.{v} R) c}

/-- The map of cycles in degree `i` induced by a morphism of complexes of modules is an
isomorphism as soon as it is injective and surjective on the kernels of the differentials out
of degree `i`. -/
theorem isIso_cyclesMap_of_bijective (φ : K ⟶ L) (i j : ι) (hj : c.next i = j)
    (hinj : ∀ x : K.X i, K.d i j x = 0 → φ.f i x = 0 → x = 0)
    (hsurj : ∀ y : L.X i, L.d i j y = 0 → ∃ x : K.X i, K.d i j x = 0 ∧ φ.f i x = y) :
    IsIso (cyclesMap φ i) := by
  subst hj
  have hKi : Function.Injective (K.iCycles i) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hLi : Function.Injective (L.iCycles i) :=
    (ModuleCat.mono_iff_injective _).mp inferInstance
  have hmap : ∀ a : K.cycles i, L.iCycles i (cyclesMap φ i a) = φ.f i (K.iCycles i a) :=
    fun a => congr($(cyclesMap_i φ i) a)
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero (cyclesMap φ i).hom).mpr fun a ha => ?_
    refine hKi ?_
    rw [map_zero]
    refine hinj _ (congr($(K.iCycles_d i (c.next i)) a)) ?_
    rw [← hmap a, ha, map_zero]
  · intro b
    obtain ⟨x, hx, hxy⟩ := hsurj (L.iCycles i b) (congr($(L.iCycles_d i (c.next i)) b))
    obtain ⟨a, ha⟩ := K.exists_iCycles_eq i x hx
    exact ⟨a, hLi (by rw [hmap a, ha, hxy])⟩

/-- The map of opcycles in degree `j` induced by a morphism of complexes of modules is an
isomorphism as soon as it is injective and surjective on the cokernels of the differentials
into degree `j`. -/
theorem isIso_opcyclesMap_of_bijective (φ : K ⟶ L) (i j : ι) (hi : c.prev j = i)
    (hinj : ∀ x : K.X j, (∃ y : L.X i, L.d i j y = φ.f j x) → ∃ z : K.X i, K.d i j z = x)
    (hsurj : ∀ y : L.X j, ∃ (x : K.X j) (z : L.X i), φ.f j x + L.d i j z = y) :
    IsIso (opcyclesMap φ j) := by
  subst hi
  have hKp : Function.Surjective (K.pOpcycles j) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hLp : Function.Surjective (L.pOpcycles j) :=
    (ModuleCat.epi_iff_surjective _).mp inferInstance
  have hmap : ∀ x : K.X j, opcyclesMap φ j (K.pOpcycles j x) = L.pOpcycles j (φ.f j x) :=
    fun x => congr($(p_opcyclesMap φ j) x)
  refine (ConcreteCategory.isIso_iff_bijective _).mpr ⟨?_, ?_⟩
  · refine (injective_iff_map_eq_zero (opcyclesMap φ j).hom).mpr fun a ha => ?_
    obtain ⟨x, rfl⟩ := hKp a
    obtain ⟨z, hz⟩ := hinj x (L.exists_d_eq_of_pOpcycles_eq_zero j _ (by rw [← hmap x, ha]))
    rw [← hz]
    exact congr($(K.d_pOpcycles (c.prev j) j) z)
  · intro b
    obtain ⟨y, rfl⟩ := hLp b
    obtain ⟨x, z, hxz⟩ := hsurj y
    have hz : L.pOpcycles j (L.d (c.prev j) j z) = 0 :=
      congr($(L.d_pOpcycles (c.prev j) j) z)
    exact ⟨K.pOpcycles j x, by rw [hmap x, ← hxz, map_add, hz, add_zero]⟩

/-- A morphism of complexes of modules is a quasi-isomorphism in a degree with no incoming
differential as soon as it is injective and surjective on the kernels of the differentials out
of that degree. -/
theorem quasiIsoAt_of_bijective_cycles (φ : K ⟶ L) (i j k : ι) (hj : c.next i = j)
    (hk : c.prev i = k) (hdK : K.d k i = 0) (hdL : L.d k i = 0)
    (hinj : ∀ x : K.X i, K.d i j x = 0 → φ.f i x = 0 → x = 0)
    (hsurj : ∀ y : L.X i, L.d i j y = 0 → ∃ x : K.X i, K.d i j x = 0 ∧ φ.f i x = y) :
    QuasiIsoAt φ i :=
  (quasiIsoAt_iff_isIso_homologyMap φ i).mpr
    (isIso_homologyMap_of_isIso_cyclesMap φ i k hk hdK hdL
      (isIso_cyclesMap_of_bijective φ i j hj hinj hsurj))

/-- A morphism of complexes of modules is a quasi-isomorphism in a degree with no outgoing
differential as soon as it is injective and surjective on the cokernels of the differentials
into that degree. -/
theorem quasiIsoAt_of_bijective_opcycles (φ : K ⟶ L) (i j k : ι) (hi : c.prev j = i)
    (hk : c.next j = k) (hdK : K.d j k = 0) (hdL : L.d j k = 0)
    (hinj : ∀ x : K.X j, (∃ y : L.X i, L.d i j y = φ.f j x) → ∃ z : K.X i, K.d i j z = x)
    (hsurj : ∀ y : L.X j, ∃ (x : K.X j) (z : L.X i), φ.f j x + L.d i j z = y) :
    QuasiIsoAt φ j :=
  (quasiIsoAt_iff_isIso_homologyMap φ j).mpr
    (isIso_homologyMap_of_isIso_opcyclesMap φ j k hk hdK hdL
      (isIso_opcyclesMap_of_bijective φ i j hi hinj hsurj))

end ModuleCat

end HomologicalComplex

namespace CochainComplex

section Abelian

variable {C : Type*} [Category* C] [Abelian C] {K L : CochainComplex C ℤ}

/-- A morphism of cochain complexes vanishing outside degrees `-1` and `0` is a
quasi-isomorphism as soon as it induces an isomorphism on the cycles in degree `-1` and on the
opcycles in degree `0`. -/
private theorem quasiIso_of_isZero_X_of_isIso_cyclesMap_opcyclesMap (φ : K ⟶ L)
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i))
    (hL : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (L.X i))
    (hcyc : IsIso (HomologicalComplex.cyclesMap φ (-1)))
    (hopcyc : IsIso (HomologicalComplex.opcyclesMap φ 0)) : QuasiIso φ := by
  refine (HomologicalComplex.quasiIso_iff_of_isZero_X φ (-1) 0 hK hL).mpr ⟨?_, ?_⟩
  · refine (quasiIsoAt_iff_isIso_homologyMap φ (-1)).mpr ?_
    exact HomologicalComplex.isIso_homologyMap_of_isIso_cyclesMap φ (-1) (-2)
      (by simp [CochainComplex.prev])
      ((hK (-2) (by decide) (by decide)).eq_of_src _ _)
      ((hL (-2) (by decide) (by decide)).eq_of_src _ _) hcyc
  · refine (quasiIsoAt_iff_isIso_homologyMap φ 0).mpr ?_
    exact HomologicalComplex.isIso_homologyMap_of_isIso_opcyclesMap φ 0 1
      (by simp [CochainComplex.next])
      ((hK 1 (by decide) (by decide)).eq_of_tgt _ _)
      ((hL 1 (by decide) (by decide)).eq_of_tgt _ _) hopcyc

/-- **Quasi-isomorphy of a two-term complex in an abelian category.**  A morphism of cochain
complexes which vanish outside degrees `-1` and `0` is a quasi-isomorphism as soon as the maps
it induces on the kernel and on the cokernel of the single differential `d : X⁻¹ ⟶ X⁰` are
isomorphisms.

Outside the two degrees both complexes vanish, so there is nothing to check there; in degree
`-1` nothing maps in, so homology is cycles, which is the kernel of the differential; and in
degree `0` nothing maps out, so homology is opcycles, which is its cokernel. -/
theorem quasiIso_of_isZero_X_of_isIso_kernel_cokernel (φ : K ⟶ L)
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i))
    (hL : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (L.X i))
    (hker : IsIso (kernel.map (K.d (-1) 0) (L.d (-1) 0) (φ.f (-1)) (φ.f 0)
      (φ.comm (-1) 0).symm))
    (hcoker : IsIso (cokernel.map (K.d (-1) 0) (L.d (-1) 0) (φ.f (-1)) (φ.f 0)
      (φ.comm (-1) 0).symm)) :
    QuasiIso φ := by
  exact quasiIso_of_isZero_X_of_isIso_cyclesMap_opcyclesMap φ hK hL
    (HomologicalComplex.isIso_cyclesMap_of_isIso_kernelMap φ (-1) 0 (by simp [CochainComplex.next])
      hker)
    (HomologicalComplex.isIso_opcyclesMap_of_isIso_cokernelMap φ (-1) 0
      (by simp [CochainComplex.prev]) hcoker)

end Abelian

variable {R : Type u} [Ring R] {K L : CochainComplex (ModuleCat.{v} R) ℤ}

/-- **Quasi-isomorphy of a two-term complex of modules.** A morphism of cochain complexes of
modules which vanish outside degrees `-1` and `0` is a quasi-isomorphism as soon as it is
bijective on the kernel and on the cokernel of the single differential `d : X⁻¹ ⟶ X⁰`. -/
theorem quasiIso_of_isZero_X_of_bijective (φ : K ⟶ L)
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i))
    (hL : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (L.X i))
    (hinjKer : ∀ x : K.X (-1), K.d (-1) 0 x = 0 → φ.f (-1) x = 0 → x = 0)
    (hsurjKer : ∀ y : L.X (-1), L.d (-1) 0 y = 0 →
      ∃ x : K.X (-1), K.d (-1) 0 x = 0 ∧ φ.f (-1) x = y)
    (hinjCoker : ∀ x : K.X 0, (∃ y : L.X (-1), L.d (-1) 0 y = φ.f 0 x) →
      ∃ z : K.X (-1), K.d (-1) 0 z = x)
    (hsurjCoker : ∀ y : L.X 0, ∃ (x : K.X 0) (z : L.X (-1)), φ.f 0 x + L.d (-1) 0 z = y) :
    QuasiIso φ := by
  exact quasiIso_of_isZero_X_of_isIso_cyclesMap_opcyclesMap φ hK hL
    (HomologicalComplex.isIso_cyclesMap_of_bijective φ (-1) 0 (by simp [CochainComplex.next])
      hinjKer hsurjKer)
    (HomologicalComplex.isIso_opcyclesMap_of_bijective φ (-1) 0 (by simp [CochainComplex.prev])
      hinjCoker hsurjCoker)

/-- **Quasi-isomorphy of a two-term complex of modules, read through equalities of its terms.**
A morphism of cochain complexes of modules which vanish outside degrees `-1` and `0` is a
quasi-isomorphism as soon as its differentials and its two nonzero components, rewritten as
conjugates by equalities of the four nonzero terms, are bijective on the kernel and on the
cokernel. -/
theorem quasiIso_of_isZero_X_of_eqToHom (φ : K ⟶ L)
    (hK : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (K.X i))
    (hL : ∀ i : ℤ, i ≠ -1 → i ≠ 0 → IsZero (L.X i))
    {C₁ T₁ C₂ T₂ : ModuleCat.{v} R} (dK : C₁ ⟶ T₁) (dL : C₂ ⟶ T₂) (pc : C₁ ⟶ C₂)
    (pt : T₁ ⟶ T₂) (e₁ : K.X (-1) = C₁) (e₀ : K.X 0 = T₁) (g₁ : L.X (-1) = C₂)
    (g₀ : L.X 0 = T₂)
    (hdK : K.d (-1) 0 = eqToHom e₁ ≫ dK ≫ eqToHom e₀.symm)
    (hdL : L.d (-1) 0 = eqToHom g₁ ≫ dL ≫ eqToHom g₀.symm)
    (hp : φ.f (-1) = eqToHom e₁ ≫ pc ≫ eqToHom g₁.symm)
    (hq : φ.f 0 = eqToHom e₀ ≫ pt ≫ eqToHom g₀.symm)
    (hinjKer : ∀ m : C₁, dK m = 0 → pc m = 0 → m = 0)
    (hsurjKer : ∀ m : C₂, dL m = 0 → ∃ n : C₁, dK n = 0 ∧ pc n = m)
    (hinjCoker : ∀ n : T₁, (∃ m : C₂, dL m = pt n) → ∃ z : C₁, dK z = n)
    (hsurjCoker : ∀ n : T₂, ∃ (m : T₁) (z : C₂), pt m + dL z = n) :
    QuasiIso φ := by
  subst e₁ e₀ g₁ g₀
  simp only [eqToHom_refl, Category.id_comp, Category.comp_id] at hdK hdL hp hq
  subst hdK hdL hp hq
  exact quasiIso_of_isZero_X_of_bijective φ hK hL hinjKer hsurjKer hinjCoker hsurjCoker

end CochainComplex

/-! ### Transport of the elementary conditions along additive identifications -/

namespace CochainComplex

variable {C₁ T₁ C₂ T₂ M₁ N₁ M₂ N₂ : Type*} [AddCommGroup C₁] [AddCommGroup T₁]
  [AddCommGroup C₂] [AddCommGroup T₂] [AddCommGroup M₁] [AddCommGroup N₁] [AddCommGroup M₂]
  [AddCommGroup N₂] {u₁ : C₁ ≃+ M₁} {u₀ : T₁ ≃+ N₁} {v₁ : C₂ ≃+ M₂} {v₀ : T₂ ≃+ N₂}
  {dK : C₁ → T₁} {dL : C₂ → T₂} {pc : C₁ → C₂} {pt : T₁ → T₂}
  {d₁ : M₁ → N₁} {d₂ : M₂ → N₂} {p : M₁ → M₂} {q : N₁ → N₂}

/-- Injectivity on the kernel of the differential transported along additive identifications
of the source and target of each of the two differentials. -/
theorem eq_zero_of_d_eq_zero_of_addEquiv
    (hdK : ∀ z, u₀ (dK z) = d₁ (u₁ z)) (hp : ∀ z, v₁ (pc z) = p (u₁ z))
    (h : ∀ m : M₁, d₁ m = 0 → p m = 0 → m = 0) (m : C₁) (h1 : dK m = 0) (h2 : pc m = 0) :
    m = 0 := by
  refine u₁.injective ((h (u₁ m) ?_ ?_).trans (map_zero u₁).symm)
  · rw [← hdK, h1, map_zero]
  · rw [← hp, h2, map_zero]

/-- Surjectivity on the kernel of the differential transported along additive identifications
of the source and target of each of the two differentials. -/
theorem exists_of_d_eq_zero_of_addEquiv
    (hdK : ∀ z, u₀ (dK z) = d₁ (u₁ z)) (hdL : ∀ z, v₀ (dL z) = d₂ (v₁ z))
    (hp : ∀ z, v₁ (pc z) = p (u₁ z))
    (h : ∀ m : M₂, d₂ m = 0 → ∃ n : M₁, d₁ n = 0 ∧ p n = m)
    (m : C₂) (h1 : dL m = 0) : ∃ n : C₁, dK n = 0 ∧ pc n = m := by
  obtain ⟨n, hn₁, hn₂⟩ := h (v₁ m) (by rw [← hdL, h1, map_zero])
  refine ⟨u₁.symm n, u₀.injective ?_, v₁.injective ?_⟩
  · rw [hdK, u₁.apply_symm_apply, hn₁, map_zero]
  · rw [hp, u₁.apply_symm_apply, hn₂]

/-- Injectivity on the cokernel of the differential transported along additive identifications
of the source and target of each of the two differentials. -/
theorem exists_d_eq_of_addEquiv
    (hdK : ∀ z, u₀ (dK z) = d₁ (u₁ z)) (hdL : ∀ z, v₀ (dL z) = d₂ (v₁ z))
    (hq : ∀ z, v₀ (pt z) = q (u₀ z))
    (h : ∀ n : N₁, (∃ m : M₂, d₂ m = q n) → ∃ z : M₁, d₁ z = n)
    (n : T₁) (hn : ∃ m : C₂, dL m = pt n) : ∃ z : C₁, dK z = n := by
  obtain ⟨m, hm⟩ := hn
  obtain ⟨z, hz⟩ := h (u₀ n) ⟨v₁ m, by rw [← hdL, hm, hq]⟩
  exact ⟨u₁.symm z, u₀.injective (by rw [hdK, u₁.apply_symm_apply, hz])⟩

/-- Surjectivity on the cokernel of the differential transported along additive identifications
of the source and target of each of the two differentials. -/
theorem exists_add_d_eq_of_addEquiv
    (hdL : ∀ z, v₀ (dL z) = d₂ (v₁ z)) (hq : ∀ z, v₀ (pt z) = q (u₀ z))
    (h : ∀ n : N₂, ∃ (m : N₁) (z : M₂), q m + d₂ z = n) (n : T₂) :
    ∃ (m : T₁) (z : C₂), pt m + dL z = n := by
  obtain ⟨m, z, hmz⟩ := h (v₀ n)
  refine ⟨u₀.symm m, v₁.symm z, v₀.injective ?_⟩
  rw [map_add, hq, hdL, u₀.apply_symm_apply, v₁.apply_symm_apply, hmz]

end CochainComplex

end
