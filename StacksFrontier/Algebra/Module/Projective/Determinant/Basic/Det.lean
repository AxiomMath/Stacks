module

public import StacksFrontier.Algebra.Module.Projective.Determinant.Basic.Invertible

/-!
# Induced maps of determinant lines and the determinant

A linear map between two modules of equal local rank induces a map of determinant lines, an
equivalence when the map is one, and an endomorphism of `M` therefore acts on the determinant
line by a unique scalar: its *determinant*.

## Main definitions

* `ProjectiveDeterminant.map`, `ProjectiveDeterminant.mapEquiv`: the induced map and equivalence
  of determinant lines.
* `ProjectiveDeterminant.det`: the scalar by which an endomorphism acts on the determinant line.

## Main results

* `ProjectiveDeterminant.det_comp`, `ProjectiveDeterminant.det_eq_linearMap_det_of_basis`:
  multiplicativity and agreement with the determinant of a matrix.
-/

namespace ProjectiveDeterminant

section

universe u v w

@[expose] public section

open scoped BigOperators

variable {R : Type u} [CommRing R]
variable {M : Type v} [AddCommGroup M] [Module R M]

variable {N : Type w} [AddCommGroup N] [Module R N]

/-- An idempotent whose basic open set is the rank `n` locus is the rank `n` idempotent. -/
private theorem rankIdempotent_eq_of_rankLocus_eq [Module.Finite R M] [Module.Projective R M]
    {n : ℕ} {e : R} (he : IsIdempotentElem e)
    (h : rankLocus (R := R) M n = (PrimeSpectrum.basicOpen e : Set (PrimeSpectrum R))) :
    rankIdempotent (R := R) (M := M) n = e :=
  ((Classical.choose_spec
    (PrimeSpectrum.existsUnique_idempotent_basicOpen_eq_of_isClopen
      (rankLocus_isClopen (R := R) (M := M) n))).2 e ⟨he, h⟩).symm

/-- Exterior algebra maps preserve determinant lines when source and target have the same
rank at every prime. -/
public theorem map_mem [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = Module.rankAtStalk N p)
    (f : M →ₗ[R] N) (x : module (R := R) (M := M)) :
    ExteriorAlgebra.map f (inclusion x) ∈ submodule (R := R) (M := N) := by
  have hId (n : ℕ) : rankIdempotent (R := R) (M := M) n =
      rankIdempotent (R := R) (M := N) n := by
    have hs : rankLocus (R := R) M n = rankLocus (R := R) N n := by
      ext p
      change Module.rankAtStalk M p = n ↔ Module.rankAtStalk N p = n
      rw [h p]
    exact rankIdempotent_eq_of_rankLocus_eq (rankIdempotent_spec (R := R) (M := N) n).1
      (hs.trans (rankIdempotent_spec (R := R) (M := N) n).2)
  have hp (n : ℕ) : (⋀[R]^n M).map (ExteriorAlgebra.map f).toLinearMap ≤
      ⋀[R]^n N := by
    rw [← ExteriorAlgebra.ιMulti_span_fixedDegree (R := R) (M := M) n,
      ← ExteriorAlgebra.ιMulti_span_fixedDegree (R := R) (M := N) n,
      Submodule.map_span]
    apply Submodule.span_mono
    rintro _ ⟨a, ⟨v, rfl⟩, rfl⟩
    exact ⟨f ∘ v, by simp⟩
  have hcomp (n : ℕ) :
      (component (R := R) (M := M) n).map (ExteriorAlgebra.map f).toLinearMap ≤
        component (R := R) (M := N) n := by
    intro y hy
    obtain ⟨z, hz, rfl⟩ := Submodule.mem_map.mp hy
    obtain ⟨a, ha, rfl⟩ := Submodule.mem_map.mp hz
    apply Submodule.mem_map.mpr
    refine ⟨ExteriorAlgebra.map f a, hp n (Submodule.mem_map_of_mem ha), ?_⟩
    simp [hId n]
  have hsub : (submodule (R := R) (M := M)).map
      (ExteriorAlgebra.map f).toLinearMap ≤ submodule (R := R) (M := N) := by
    change (⨆ n, component (R := R) (M := M) n).map
      (ExteriorAlgebra.map f).toLinearMap ≤ _
    rw [Submodule.map_iSup]
    exact iSup_le fun n => (hcomp n).trans (component_le_submodule n)
  exact hsub (Submodule.mem_map_of_mem x.2)

/-- The determinant map induced by a linear map between finite projective modules having
equal rank at every prime. -/
public noncomputable def map [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    (h : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = Module.rankAtStalk N p)
    (f : M →ₗ[R] N) : module (R := R) (M := M) →ₗ[R] module (R := R) (M := N) :=
  ((ExteriorAlgebra.map f).toLinearMap.comp (inclusion (R := R) (M := M))).codRestrict
    (submodule (R := R) (M := N)) (map_mem h f)

/-- The determinant map of the identity is the identity. -/
public theorem map_id [Module.Finite R M] [Module.Projective R M] :
    map (M := M) (N := M) (fun _ => rfl) (LinearMap.id : M →ₗ[R] M) =
      (LinearMap.id : module (R := R) (M := M) →ₗ[R] module (R := R) (M := M)) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  simp [map, inclusion]

/-- Determinant maps respect composition. -/
public theorem map_comp {P : Type*} [AddCommGroup P] [Module R P]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    [Module.Finite R P] [Module.Projective R P]
    (hMN : ∀ p : PrimeSpectrum R, Module.rankAtStalk M p = Module.rankAtStalk N p)
    (hNP : ∀ p : PrimeSpectrum R, Module.rankAtStalk N p = Module.rankAtStalk P p)
    (f : M →ₗ[R] N) (g : N →ₗ[R] P) :
    map (M := M) (N := P) (fun p => (hMN p).trans (hNP p)) (g.comp f) =
      (map hNP g).comp (map hMN f) := by
  apply LinearMap.ext
  intro x
  apply Subtype.ext
  change ExteriorAlgebra.map (g.comp f) x.1 =
    ExteriorAlgebra.map g (ExteriorAlgebra.map f x.1)
  rw [← ExteriorAlgebra.map_comp_map]
  rfl

/-- Linearly equivalent finite projective modules have the same rank at every prime. -/
public theorem rankAtStalk_congr [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (e : M ≃ₗ[R] N)
    (p : PrimeSpectrum R) : Module.rankAtStalk M p = Module.rankAtStalk N p := by
  exact congrFun (Module.rankAtStalk_eq_of_equiv e) p

/-- The determinant map of a linear equivalence is bijective. -/
public theorem map_bijective [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (e : M ≃ₗ[R] N) :
    Function.Bijective
      (map (fun p => rankAtStalk_congr e p) e.toLinearMap) := by
  let F := map (fun p => rankAtStalk_congr e p) e.toLinearMap
  let G := map (fun p => (rankAtStalk_congr e p).symm) e.symm.toLinearMap
  have hGF (x : module (R := R) (M := M)) : G (F x) = x := by
    apply Subtype.ext
    change ExteriorAlgebra.map e.symm.toLinearMap
      (ExteriorAlgebra.map e.toLinearMap x.1) = x.1
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    simp
  have hFG (y : module (R := R) (M := N)) : F (G y) = y := by
    apply Subtype.ext
    change ExteriorAlgebra.map e.toLinearMap
      (ExteriorAlgebra.map e.symm.toLinearMap y.1) = y.1
    rw [← AlgHom.comp_apply, ExteriorAlgebra.map_comp_map]
    simp
  exact ⟨fun x y h => (hGF x).symm.trans ((congrArg G h).trans (hGF y)),
    fun y => ⟨G y, hFG y⟩⟩

/-- The canonical equivalence of determinant lines induced by an equivalence of finite
projective modules. -/
public noncomputable def mapEquiv [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N] (e : M ≃ₗ[R] N) :
    module (R := R) (M := M) ≃ₗ[R] module (R := R) (M := N) :=
  LinearEquiv.ofBijective (map (fun p => rankAtStalk_congr e p) e.toLinearMap)
    (map_bijective e)

/-- An endomorphism of an invertible module is scalar multiplication by a unique scalar. -/
public theorem existsUnique_scalar [Module.Finite R M] [Module.Projective R M]
    (f : module (R := R) (M := M) →ₗ[R] module (R := R) (M := M)) :
    ∃! r : R, f = r • LinearMap.id := by
  let := invertible (R := R) (M := M)
  have hsmul (t : R) : Module.toModuleEnd R (module (R := R) (M := M)) t =
      t • LinearMap.id := by
    ext x
    rfl
  obtain ⟨r, hr⟩ := (Module.Invertible.toModuleEnd_bijective R
    (module (R := R) (M := M))).2 f
  refine ⟨r, ?_, ?_⟩
  · simpa only [hsmul] using hr.symm
  · intro s hs
    apply (Module.Invertible.toModuleEnd_bijective R
      (module (R := R) (M := M))).1
    rw [hsmul, hsmul]
    exact hs.symm.trans (by simpa only [hsmul] using hr.symm)

/-- The scalar determinant of an endomorphism of a finite projective module. -/
public noncomputable def det [Module.Finite R M] [Module.Projective R M]
    (f : M →ₗ[R] M) : R :=
  Classical.choose (existsUnique_scalar (M := M) (map (fun _ => rfl) f))

/-- The determinant line map of an endomorphism is multiplication by its determinant. -/
private theorem map_eq_det_smul [Module.Finite R M] [Module.Projective R M]
    (f : M →ₗ[R] M) : map (fun _ => rfl) f = det f • LinearMap.id :=
  (Classical.choose_spec (existsUnique_scalar (M := M) (map (fun _ => rfl) f))).1

/-- The determinant of a composite is the product of the determinants. -/
public theorem det_comp [Module.Finite R M] [Module.Projective R M]
    (f g : M →ₗ[R] M) : det (g.comp f) = det g * det f := by
  have hresult : map (fun _ => rfl) (g.comp f) =
      (det g * det f) • LinearMap.id := by
    rw [map_comp (fun _ => rfl) (fun _ => rfl), map_eq_det_smul f, map_eq_det_smul g]
    ext x
    simp [mul_smul]
  exact (existsUnique_scalar (M := M) _).unique (map_eq_det_smul _) hresult

/-- On the unique rank stratum of a finite free module, the canonical rank idempotent is one. -/
public theorem rankIdempotent_eq_one_of_free [Module.Finite R M] [Module.Free R M] :
    rankIdempotent (R := R) (M := M) (Module.finrank R M) = 1 := by
  refine rankIdempotent_eq_of_rankLocus_eq (by simp [IsIdempotentElem]) ?_
  ext p
  simp [rankLocus]

/-- For a finite free module, the projective determinant agrees with the usual determinant. -/
public theorem det_eq_linearMap_det_of_basis [Nontrivial R]
    [Module.Finite R M] [Module.Projective R M]
    {n : ℕ} (b : Module.Basis (Fin n) R M) (f : M →ₗ[R] M) :
    det f = LinearMap.det f := by
  classical
  let : Module.Free R M := Module.Free.of_basis b
  have hn : Module.finrank R M = n := by
    rw [Module.finrank_eq_card_basis b, Fintype.card_fin]
  let w : ExteriorAlgebra R M := ExteriorAlgebra.ιMulti R n b
  have hwdeg : w ∈ ⋀[R]^n M := by
    exact ExteriorAlgebra.ιMulti_range R n ⟨b, rfl⟩
  have hwcomp : w ∈ component (R := R) (M := M) n := by
    apply Submodule.mem_map.mpr
    refine ⟨w, hwdeg, ?_⟩
    have hid : rankIdempotent (R := R) (M := M) n = 1 := by
      rw [← hn]
      exact rankIdempotent_eq_one_of_free (R := R) (M := M)
    rw [hid]
    simp
  let x : module (R := R) (M := M) :=
    ⟨w, component_le_submodule (R := R) (M := M) n hwcomp⟩
  have hmap : map (M := M) (N := M) (fun _ => rfl) f x = det f • x := by
    rw [map_eq_det_smul f]
    rfl
  have hw : ExteriorAlgebra.map f w = det f • w := by
    exact congrArg Subtype.val hmap
  have hw' : ExteriorAlgebra.ιMulti R n (f ∘ b) = det f • ExteriorAlgebra.ιMulti R n b := by
    simpa [w, ExteriorAlgebra.map_apply_ιMulti] using hw
  let s : Set.powersetCard (Fin n) n := ⟨Finset.univ, by simp⟩
  have hleft : ExteriorAlgebra.ιMulti R n (f ∘ b) ∈ ⋀[R]^n M :=
    ExteriorAlgebra.ιMulti_range R n ⟨f ∘ b, rfl⟩
  have hright : det f • ExteriorAlgebra.ιMulti R n b ∈ ⋀[R]^n M :=
    (Submodule.smul_mem _ _ hwdeg)
  have heq : (⟨_, hleft⟩ : ⋀[R]^n M) = ⟨_, hright⟩ := Subtype.ext hw'
  have hcoeff := congrArg (exteriorPower.ιMultiDual R n b s) heq
  change exteriorPower.ιMultiDual R n b s (exteriorPower.ιMulti R n (f ∘ b)) =
    exteriorPower.ιMultiDual R n b s (det f • exteriorPower.ιMulti R n b) at hcoeff
  rw [exteriorPower.ιMultiDual_apply_ιMulti, map_smul,
    exteriorPower.ιMultiDual_apply_ιMulti] at hcoeff
  have hs (i : Fin n) : Set.powersetCard.ofFinEmbEquiv.symm s i = i := by
    change Finset.orderEmbOfFin Finset.univ _ i = i
    symm
    exact congrFun (Finset.orderEmbOfFin_unique (by simp) (fun _ => Finset.mem_univ _)
      strictMono_id) i
  have hmatrix :
      Matrix.of (fun i j => b.coord (Set.powersetCard.ofFinEmbEquiv.symm s j) (f (b i))) =
        Matrix.transpose (LinearMap.toMatrix b b f) := by
    ext i j
    simp [hs, LinearMap.toMatrix_apply]
  simp only [Function.comp_apply] at hcoeff
  rw [hmatrix, Matrix.det_transpose, LinearMap.det_toMatrix] at hcoeff
  have hident : Matrix.of (fun i j => b.coord
      (Set.powersetCard.ofFinEmbEquiv.symm s j) (b i)) = 1 := by
    ext i j
    by_cases h : i = j
    · subst j
      simp [hs]
    · simp [hs, h]
  rw [hident, Matrix.det_one, smul_eq_mul, mul_one] at hcoeff
  exact hcoeff.symm

/-- The projective determinant satisfies the Weinstein--Aronszajn identity on finite free
modules. The chosen bases may have different finite cardinalities. -/
public theorem det_one_add_comp_comm_of_basis [Nontrivial R]
    [Module.Finite R M] [Module.Projective R M]
    [Module.Finite R N] [Module.Projective R N]
    {m n : ℕ} (bM : Module.Basis (Fin m) R M) (bN : Module.Basis (Fin n) R N)
    (a : M →ₗ[R] N) (b : N →ₗ[R] M) :
    det (LinearMap.id + b.comp a) = det (LinearMap.id + a.comp b) := by
  rw [det_eq_linearMap_det_of_basis bM, det_eq_linearMap_det_of_basis bN,
    ← LinearMap.det_toMatrix bM, ← LinearMap.det_toMatrix bN]
  simp only [map_add, LinearMap.toMatrix_id]
  rw [LinearMap.toMatrix_comp bM bN bM, LinearMap.toMatrix_comp bN bM bN]
  exact Matrix.det_one_add_mul_comm (LinearMap.toMatrix bN bM b) (LinearMap.toMatrix bM bN a)

/-- For a finite free module the determinant line is its top exterior power. -/
@[sga "6 X 6.2" "special case"]
public theorem submodule_eq_exteriorPower_of_free
    [Module.Finite R M] [Module.Free R M] :
    submodule (R := R) (M := M) = ⋀[R]^(Module.finrank R M) M := by
  classical
  have hzero (k : ℕ) (hk : Module.finrank R M ≠ k) :
      rankIdempotent (R := R) (M := M) k = 0 := by
    refine rankIdempotent_eq_of_rankLocus_eq (by simp [IsIdempotentElem]) ?_
    ext p
    simp [rankLocus, hk]
  apply le_antisymm
  · apply iSup_le
    intro k
    by_cases hk : Module.finrank R M = k
    · subst k
      simp [component, rankIdempotent_eq_one_of_free]
    · simp [component, hzero k hk]
  · have h := component_le_submodule (R := R) (M := M) (Module.finrank R M)
    simpa [component, rankIdempotent_eq_one_of_free] using h

end

end

end ProjectiveDeterminant
