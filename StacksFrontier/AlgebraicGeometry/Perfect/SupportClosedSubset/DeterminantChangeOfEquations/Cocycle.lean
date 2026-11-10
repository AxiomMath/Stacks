module

public import
 StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DeterminantChangeOfEquations.Subfamily

/-!
# The mixed cocycle of a change of equations

The mixed family of `2c` equations of a change of equations, the cocycle `mixedFractionHom` on its
extended alternating Čech complex and its two projections (Stacks 0G7S at the level of the
complexes), cohomology classes of cocycles, and the cokernel of the last differential as the
degree-`c` cohomology.
Part of `StacksFrontier.AlgebraicGeometry.Perfect.SupportClosedSubset.DeterminantChangeOfEquations`.

* [Stacks Project, Tag 0G7S](https://stacks.math.columbia.edu/tag/0G7S)
-/

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits TopologicalSpace Opposite
open Stacks.AlgebraicGeometry.ModuleLimits (homOfSections homOfSections_app)
open Stacks.Perfect.ExtendedAlternatingCech
open scoped AlgebraicGeometry

universe u

namespace Stacks.Perfect.SupportedFraction

attribute [local instance] Classical.propDecidable

variable {X : Scheme.{u}}

/-! ### The mixed family of a change of equations -/

section Mixed

variable {d : ℕ}

/-- The family of `2c` equations obtained by listing `f₁, …, f_c` and then `g₁, …, g_c`. -/
public def mixedEquations (f g : Fin (d + 1) → Γ(X, ⊤)) :
    Fin ((d + 1) + (d + 1)) → Γ(X, ⊤) :=
  Fin.append f g

/-- The first half of the mixed family is the first family. -/
public theorem mixedEquations_comp_castAdd (f g : Fin (d + 1) → Γ(X, ⊤)) :
    mixedEquations f g ∘ (Fin.castAddOrderEmb (d + 1) : Fin (d + 1) ↪o Fin ((d + 1) + (d + 1)))
      = f :=
  funext fun i => Fin.append_left f g i

/-- The second half of the mixed family is the second family. -/
public theorem mixedEquations_comp_natAdd (f g : Fin (d + 1) → Γ(X, ⊤)) :
    mixedEquations f g ∘ (Fin.natAddOrderEmb (d + 1) : Fin (d + 1) ↪o Fin ((d + 1) + (d + 1)))
      = g :=
  funext fun j => Fin.append_right f g j

/-- The `2c × c` matrix of coefficients expressing each member of the mixed family in terms of
`f₁, …, f_c`: the first `c` rows are the rows of the identity matrix, the last `c` rows are the
rows of the change-of-equations matrix. -/
public def mixedRows (a : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(X, ⊤)) :
    Fin ((d + 1) + (d + 1)) → Fin (d + 1) → Γ(X, ⊤) :=
  Fin.append (fun i j => if i = j then (1 : Γ(X, ⊤)) else 0) (fun i j => a i j)

/-- The `c × c` minor of the coefficient matrix selected by an increasing `c`-tuple of indices
of the mixed family.  Its determinant is the coefficient of the mixed fraction indexed by that
tuple: for the tuple listing `f₁, …, f_c` it is `1`, and for the tuple listing `g₁, …, g_c` it
is `det(a_{ji})`. -/
public def mixedMinor (a : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(X, ⊤))
    (q : CechCochains.OrdIndex (I := Fin ((d + 1) + (d + 1))) d) :
    Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(X, ⊤) :=
  Matrix.of fun r j => mixedRows a (q.1 r) j

/-- Each member of the mixed family is the corresponding row of the coefficient matrix applied
to `f₁, …, f_c`. -/
public theorem mixedEquations_eq_dot (f g : Fin (d + 1) → Γ(X, ⊤))
    (a : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(X, ⊤)) (hg : ∀ j, g j = ∑ i, a j i * f i)
    (k : Fin ((d + 1) + (d + 1))) :
    mixedEquations f g k = ∑ j, mixedRows a k j * f j := by
  refine Fin.addCases (fun i => ?_) (fun j => ?_) k
  · rw [mixedEquations, Fin.append_left, mixedRows, Fin.append_left]
    simp
  · rw [mixedEquations, Fin.append_right, mixedRows, Fin.append_right, hg j]

/-- The minor selected by the tuple listing the first half of the mixed family is the identity
matrix. -/
public theorem mixedMinor_castAdd (a : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(X, ⊤)) :
    mixedMinor a (subfamilyIndex (Fin.castAddOrderEmb (d + 1)) (topIndex d)) = 1 := by
  ext r j
  rw [mixedMinor, Matrix.of_apply,
    show (subfamilyIndex (Fin.castAddOrderEmb (d + 1)) (topIndex d)).1 r
      = Fin.castAdd (d + 1) r from rfl,
    mixedRows, Fin.append_left]
  rw [Matrix.one_apply]

/-- The minor selected by the tuple listing the second half of the mixed family is the
change-of-equations matrix. -/
public theorem mixedMinor_natAdd (a : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(X, ⊤)) :
    mixedMinor a (subfamilyIndex (Fin.natAddOrderEmb (d + 1)) (topIndex d)) = a := by
  ext r j
  rw [mixedMinor, Matrix.of_apply,
    show (subfamilyIndex (Fin.natAddOrderEmb (d + 1)) (topIndex d)).1 r
      = Fin.natAdd (d + 1) r from rfl,
    mixedRows, Fin.append_right]

/-! ### The mixed cocycle -/

variable (e : Fin ((d + 1) + (d + 1)) → Γ(X, ⊤))
  (a : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(X, ⊤)) (F : X.Modules)

/-- Multiplication of the component indexed by an increasing `c`-tuple of indices of the mixed
family by the determinant of the minor that tuple selects. -/
public def minorSmul : prodTerm e F d ⟶ prodTerm e F d :=
  Pi.lift fun q =>
    Pi.π (fun t : CechCochains.OrdIndex (I := Fin ((d + 1) + (d + 1))) d =>
      restrictedModule e F d t) q ≫
      globalSmul (mixedMinor a q).det (restrictedModule e F d q)

/-- On sections, `minorSmul` multiplies each component by the determinant of its minor. -/
public theorem secIso_minorSmul (V : X.Opens) (x : Γ(prodTerm e F d, V))
    (q : CechCochains.OrdIndex (I := Fin ((d + 1) + (d + 1))) d) :
    secIso e F d V ((minorSmul e a F).app V x) q =
      X.presheaf.map (homOfLE (show
          CechCochains.inter (fun i => V ⊓ X.basicOpen (e i)) q.1 ≤ ⊤ from le_top)).op
        (mixedMinor a q).det • secIso e F d V x q := by
  have h₁ : minorSmul e a F ≫
        Pi.π (fun t : CechCochains.OrdIndex (I := Fin ((d + 1) + (d + 1))) d =>
          restrictedModule e F d t) q =
      Pi.π (fun t : CechCochains.OrdIndex (I := Fin ((d + 1) + (d + 1))) d =>
          restrictedModule e F d t) q ≫
        globalSmul (mixedMinor a q).det (restrictedModule e F d q) := Pi.lift_comp_π _ q
  have hπ : (Pi.π (fun t : CechCochains.OrdIndex (I := Fin ((d + 1) + (d + 1))) d =>
        restrictedModule e F d t) q).app V ((minorSmul e a F).app V x) =
      appApplyHom V x (minorSmul e a F ≫
        Pi.π (fun t : CechCochains.OrdIndex (I := Fin ((d + 1) + (d + 1))) d =>
          restrictedModule e F d t) q) := rfl
  rw [secIso_apply, hπ, h₁,
    show appApplyHom V x
        (Pi.π (fun t : CechCochains.OrdIndex (I := Fin ((d + 1) + (d + 1))) d =>
            restrictedModule e F d t) q ≫
          globalSmul (mixedMinor a q).det (restrictedModule e F d q)) =
        (globalSmul (mixedMinor a q).det (restrictedModule e F d q)).app V
          ((Pi.π (fun t : CechCochains.OrdIndex (I := Fin ((d + 1) + (d + 1))) d =>
            restrictedModule e F d t) q).app V x) from rfl,
    globalSmul_app, restrictedModuleSection_smul, secIso_apply]
  congr 1
  exact ringMap_collapse (homOfLE (show V ≤ ⊤ from le_top))
    (homOfLE (interLe e d q V))
    (homOfLE (show CechCochains.inter (fun i => V ⊓ X.basicOpen (e i)) q.1 ≤ ⊤ from le_top))
    (mixedMinor a q).det

/-- The mixed cochain of Stacks 0G7S in degree `c`: its component at an increasing `c`-tuple
`q` of indices of the mixed family `f₁, …, f_c, g₁, …, g_c` is

`det(minor of the coefficient matrix selected by q) · s / (product of the equations of q)`.

At the tuple listing `f₁, …, f_c` this is `s / (f₁ ⋯ f_c)` and at the tuple listing
`g₁, …, g_c` it is `det(a_{ji}) s / (g₁ ⋯ g_c)`. -/
public def mixedFractionHom : F ⟶ prodTerm e F d :=
  fractionHom e F d ≫ minorSmul e a F

/-- The sections of the mixed cochain. -/
public theorem secIso_mixedFractionHom (V : X.Opens) (s : Γ(F, V))
    (q : CechCochains.OrdIndex (I := Fin ((d + 1) + (d + 1))) d) :
    secIso e F d V ((mixedFractionHom e a F).app V s) q =
      X.presheaf.map (homOfLE (show
          CechCochains.inter (fun i => V ⊓ X.basicOpen (e i)) q.1 ≤ ⊤ from le_top)).op
        (mixedMinor a q).det • fractionCochain e F d V s q := by
  rw [mixedFractionHom, comp_app_apply, secIso_minorSmul, fractionHom_secIso]

/-- Multiplying the component of the mixed cochain at an increasing `c`-tuple by the product of
the corresponding equations recovers the determinant of the minor times the numerator. -/
public theorem prodEquations_smul_secIso_mixedFractionHom (V : X.Opens) (s : Γ(F, V))
    (q : CechCochains.OrdIndex (I := Fin ((d + 1) + (d + 1))) d) :
    X.presheaf.map (homOfLE (show
          CechCochains.inter (fun i => V ⊓ X.basicOpen (e i)) q.1 ≤ ⊤ from le_top)).op
        (∏ k, e (q.1 k)) •
        secIso e F d V ((mixedFractionHom e a F).app V s) q =
      X.presheaf.map (homOfLE (show
          CechCochains.inter (fun i => V ⊓ X.basicOpen (e i)) q.1 ≤ ⊤ from le_top)).op
        (mixedMinor a q).det • F.presheaf.map (homOfLE (interLe e d q V)).op s := by
  rw [secIso_mixedFractionHom, smul_comm, prodEquations_smul_fractionCochain]

/-- The restriction to a `(c + 1)`-fold intersection of a face component of the mixed cochain,
multiplied by the product of all `c + 1` equations of the tuple: the Čech sign aside, this is
the term of the cocycle identity indexed by the omitted equation. -/
public theorem prodEquations_smul_face_secIso_mixedFractionHom (V : X.Opens) (s : Γ(F, V))
    (t : CechCochains.OrdIndex (I := Fin ((d + 1) + (d + 1))) (d + 1)) (j : Fin (d + 2)) :
    X.presheaf.map (homOfLE (show
          CechCochains.inter (fun i => V ⊓ X.basicOpen (e i)) t.1 ≤ ⊤ from le_top)).op
        (∏ k, e (t.1 k)) •
        F.presheaf.map (homOfLE
            (CechCochains.inter_le_omit (fun i => V ⊓ X.basicOpen (e i)) t.1 j)).op
          (secIso e F d V ((mixedFractionHom e a F).app V s)
            ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩) =
      X.presheaf.map (homOfLE (show
          CechCochains.inter (fun i => V ⊓ X.basicOpen (e i)) t.1 ≤ ⊤ from le_top)).op
        (e (t.1 j) *
          (mixedMinor a ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩).det) •
        F.presheaf.map (homOfLE (interLe e (d + 1) t V)).op s := by
  set tj : CechCochains.OrdIndex (I := Fin ((d + 1) + (d + 1))) d :=
    ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩ with htj
  set hle := CechCochains.inter_le_omit (fun i => V ⊓ X.basicOpen (e i)) t.1 j with hhle
  have key := congrArg (fun y => F.presheaf.map (homOfLE hle).op y)
    (prodEquations_smul_secIso_mixedFractionHom e a F V s tj)
  simp only [Scheme.Modules.map_smul F (homOfLE hle)] at key
  rw [ringMap_collapse (homOfLE (show
        CechCochains.inter (fun i => V ⊓ X.basicOpen (e i)) tj.1 ≤ ⊤ from le_top))
      (homOfLE hle)
      (homOfLE (show CechCochains.inter (fun i => V ⊓ X.basicOpen (e i)) t.1 ≤ ⊤ from le_top)),
    ringMap_collapse (homOfLE (show
        CechCochains.inter (fun i => V ⊓ X.basicOpen (e i)) tj.1 ≤ ⊤ from le_top))
      (homOfLE hle)
      (homOfLE (show CechCochains.inter (fun i => V ⊓ X.basicOpen (e i)) t.1 ≤ ⊤ from le_top)),
    collapse2 F (homOfLE (interLe e d tj V)) (homOfLE hle)
      (homOfLE (interLe e (d + 1) t V))] at key
  rw [show (∏ k, e (t.1 k)) = e (t.1 j) * ∏ k, e (tj.1 k) from
      Fin.prod_univ_succAbove (fun k => e (t.1 k)) j,
    map_mul, mul_smul, key, map_mul, mul_smul]

/-- Two morphisms into an extended alternating Čech term are equal if they agree on sections
after `secIso`. -/
private theorem hom_eq_of_secIso {m : ℕ} (e : Fin m → Γ(X, ⊤)) (F : X.Modules) (p : ℕ)
    (u v : F ⟶ prodTerm e F p)
    (h : ∀ (V : X.Opens) (s : Γ(F, V)),
      secIso e F p V (u.app V s) = secIso e F p V (v.app V s)) : u = v := by
  refine Scheme.Modules.hom_ext _ _ fun V => ?_
  refine AddCommGrpCat.hom_ext (AddMonoidHom.ext fun s => ?_)
  exact (secIso e F p V).injective (h V s)

/-- **The cocycle identity for the mixed cochain.**  If every member of the mixed family is the
corresponding row of the coefficient matrix applied to `f₁, …, f_c`, then the mixed cochain of
Stacks 0G7S is a cocycle: the signed sum of the determinants of the minors, weighted by the
omitted equation, vanishes by `cofactorSum_eq_zero`. -/
public theorem mixedFractionHom_difSucc {f : Fin (d + 1) → Γ(X, ⊤)}
    (hdot : ∀ k, e k = ∑ j, mixedRows a k j * f j) :
    mixedFractionHom e a F ≫ difSucc e F d = 0 := by
  refine hom_eq_of_secIso _ _ _ _ _ fun V s => ?_
  rw [comp_app_apply, secIso_difSucc,
    show (0 : F ⟶ prodTerm e F (d + 1)).app V s = 0 from rfl, map_zero]
  funext t
  rw [CechCochains.OrdCochain.zero_apply, ordD_apply]
  have hunit := isUnit_prodEquations e V (d + 1) t
  refine hunit.smul_left_cancel.mp ?_
  rw [smul_zero, Finset.smul_sum]
  have hterm : ∀ j : Fin (d + 2),
      X.presheaf.map (homOfLE (show
            CechCochains.inter (fun i => V ⊓ X.basicOpen (e i)) t.1 ≤ ⊤ from le_top)).op
          (∏ k, e (t.1 k)) •
          (((-1 : ℤ) ^ (j : ℕ)) •
            CechCochains.restr (Scheme.Modules.presheaf F)
              (CechCochains.inter_le_omit (fun i => V ⊓ X.basicOpen (e i)) t.1 j)
              (secIso e F d V ((mixedFractionHom e a F).app V s)
                ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩)) =
        X.presheaf.map (homOfLE (show
            CechCochains.inter (fun i => V ⊓ X.basicOpen (e i)) t.1 ≤ ⊤ from le_top)).op
          ((-1 : Γ(X, ⊤)) ^ (j : ℕ) * e (t.1 j) *
            (mixedMinor a ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩).det) •
          F.presheaf.map (homOfLE (interLe e (d + 1) t V)).op s := by
    intro j
    rw [smul_comm, restr_eq, prodEquations_smul_face_secIso_mixedFractionHom,
      ← Int.cast_smul_eq_zsmul (R := Γ(X, CechCochains.inter
        (fun i => V ⊓ X.basicOpen (e i)) t.1)), smul_smul]
    simp only [map_mul, map_pow, map_neg, map_one, Int.cast_pow, Int.cast_neg, Int.cast_one]
    rw [mul_assoc]
  rw [Finset.sum_congr rfl fun j _ => hterm j, ← Finset.sum_smul, ← map_sum,
    show (∑ j : Fin (d + 2), (-1 : Γ(X, ⊤)) ^ (j : ℕ) * e (t.1 j) *
          (mixedMinor a ⟨t.1 ∘ j.succAbove, CechCochains.strictMono_omit t.2 j⟩).det) = 0 from ?_,
    map_zero, zero_smul]
  have h := cofactorSum_eq_zero f (fun r => mixedRows a (t.1 r))
  refine h.symm.trans (Finset.sum_congr rfl fun j _ => ?_) |>.symm
  rw [← hdot (t.1 j)]
  rfl

/-! ### The two projections of the mixed cocycle -/

/-- **The projection of the mixed cocycle to the first half of the mixed family** is the
fraction `s / (f₁ ⋯ f_c)`: the minor selected by the tuple listing `f₁, …, f_c` is the identity
matrix, whose determinant is `1`. -/
public theorem mixedFractionHom_subfamilyProd_castAdd :
    mixedFractionHom e a F ≫
        subfamilyProd e (Fin.castAddOrderEmb (d + 1) :
          Fin (d + 1) ↪o Fin ((d + 1) + (d + 1))) F d =
      fractionHom (e ∘ (Fin.castAddOrderEmb (d + 1) :
        Fin (d + 1) ↪o Fin ((d + 1) + (d + 1)))) F d := by
  refine hom_eq_of_secIso _ _ _ _ _ fun V s => ?_
  funext q
  obtain rfl : q = topIndex d := topIndex_unique q
  rw [comp_app_apply, secIso_subfamilyProd, secIso_mixedFractionHom, fractionHom_secIso,
    mixedMinor_castAdd, Matrix.det_one, map_one, one_smul]
  rfl

/-- **The projection of the mixed cocycle to the second half of the mixed family** is
`det(a_{ji}) s / (g₁ ⋯ g_c)`: the minor selected by the tuple listing `g₁, …, g_c` is the
change-of-equations matrix itself. -/
public theorem mixedFractionHom_subfamilyProd_natAdd :
    mixedFractionHom e a F ≫
        subfamilyProd e (Fin.natAddOrderEmb (d + 1) :
          Fin (d + 1) ↪o Fin ((d + 1) + (d + 1))) F d =
      globalSmul a.det F ≫ fractionHom (e ∘ (Fin.natAddOrderEmb (d + 1) :
        Fin (d + 1) ↪o Fin ((d + 1) + (d + 1)))) F d := by
  refine hom_eq_of_secIso _ _ _ _ _ fun V s => ?_
  funext q
  obtain rfl : q = topIndex d := topIndex_unique q
  rw [comp_app_apply, comp_app_apply, secIso_subfamilyProd, secIso_mixedFractionHom,
    fractionHom_secIso, mixedMinor_natAdd, globalSmul_app, fractionCochain_smul,
    ringMap_collapse (homOfLE (show V ≤ ⊤ from le_top))
      (homOfLE (interLe (e ∘ (Fin.natAddOrderEmb (d + 1) :
        Fin (d + 1) ↪o Fin ((d + 1) + (d + 1)))) d (topIndex d) V))
      (homOfLE (show CechCochains.inter (fun i => V ⊓ X.basicOpen
          ((e ∘ (Fin.natAddOrderEmb (d + 1) :
            Fin (d + 1) ↪o Fin ((d + 1) + (d + 1)))) i)) (topIndex d).1 ≤ ⊤ from le_top))
      a.det]
  rfl

end Mixed

/-! ### Stacks 0G7S -/

section Main

variable {d : ℕ} (f g : Fin (d + 1) → Γ(X, ⊤))
  (a : Matrix (Fin (d + 1)) (Fin (d + 1)) Γ(X, ⊤)) (F : X.Modules)

/-- **Stacks Project, Tag 0G7S**, the determinant identity on the mixed extended alternating
Čech complex.

With `X`, `f₁, …, f_c ∈ Γ(X, 𝒪_X)` and `ℱ` as in Stacks 0G7I, let `a_{ji} ∈ Γ(X, 𝒪_X)` and
`g_j = ∑_i a_{ji} f_i`.  Write `𝓕''^•` for the extended alternating Čech complex of the mixed
family `f₁, …, f_c, g₁, …, g_c` of `2c` equations, which is the complex the source's proof
introduces.  Projecting away the components involving a `g`, respectively an `f`, gives the two
morphisms of complexes `𝓕''^• ⟶ 𝓕^•` and `𝓕''^• ⟶ (𝓕')^•` of the source, both the identity in
degree `0` (`subfamilyCplxMap`, whose degree-`(c)` component is `subfamilyProd`).

The content of the lemma is the explicit degree-`c` cocycle `σ = mixedFractionHom` of the
source, whose component at an increasing `c`-tuple `q` of the `2c` indices is
`det(minor of (a_{ji}) selected by q) · s / (product of the equations of q)`:

* `σ` is a cocycle;
* its projection to `𝓕^•` is `s / (f₁ ⋯ f_c)`, i.e. `c_{f₁,…,f_c}`;
* its projection to `(𝓕')^•` is `det(a_{ji}) s / (g₁ ⋯ g_c)`, i.e. `det(a_{ji}) c_{g₁,…,g_c}`.

What is **not** carried out here is the last step of the source's proof: passing from these
two projections of `σ` to the single equation `c_{f₁,…,f_c} = det(a_{ji}) c_{g₁,…,g_c}` of
sheaf maps `i^*ℱ ⟶ ℋ^c_Z(ℱ)`.  That step is the identification of the degree-`c` cohomology of
each of the three complexes with `i_*ℋ^c_Z(ℱ)`, which is Stacks 0G7M and **is** available in
this library — `Stacks.Perfect.CechDerivedSupport.isIso_map_augmentation_of_isQuasicoherent`
for the half that uses the quasi-coherence of `ℱ`, and
`isIso_derivedSupportedSectionsToId_cech` above for the canonical form of the other half.  What
is missing is only the bookkeeping that composes the two statements below with those
identifications: the comparison `cechToDerivedSupport` of Stacks 0G7L above, its degree-`c`
cohomology sheaf, and the identification of `H^c` of each complex with the cokernel of its last
differential.  The hypothesis that `g₁, …, g_c` cut out `Z` scheme theoretically is likewise
needed only for that step — it is what makes the two identifications land in the same
`i_*ℋ^c_Z(ℱ)` — and so does not appear below. -/
@[stacks 0G7S "the source's own construction: the explicit degree-c cocycle on the mixed
extended alternating Čech complex of f₁,…,f_c,g₁,…,g_c is a cocycle, and projects to
s/(f₁⋯f_c) and to det(a)·s/(g₁⋯g_c).  Stated at the level of the complexes, i.e. before the
identification of the degree-c cohomology of the three complexes with i_*ℋ^c_Z(ℱ); that
identification is Stacks 0G7M, and composing it with this statement to obtain the single
equation c_{f₁,…,f_c} = det(a_{ji})·c_{g₁,…,g_c} is carried out in this module, in
supportedFractionClass_eq_det_smul"]
public theorem mixedFractionHom_projections (hg : ∀ j, g j = ∑ i, a j i * f i) :
    mixedFractionHom (mixedEquations f g) a F ≫ difSucc (mixedEquations f g) F d = 0 ∧
      mixedFractionHom (mixedEquations f g) a F ≫
          subfamilyProd (mixedEquations f g) (Fin.castAddOrderEmb (d + 1) :
            Fin (d + 1) ↪o Fin ((d + 1) + (d + 1))) F d ≫
          prodTermCongr (mixedEquations_comp_castAdd f g) F d =
        fractionHom f F d ∧
      mixedFractionHom (mixedEquations f g) a F ≫
          subfamilyProd (mixedEquations f g) (Fin.natAddOrderEmb (d + 1) :
            Fin (d + 1) ↪o Fin ((d + 1) + (d + 1))) F d ≫
          prodTermCongr (mixedEquations_comp_natAdd f g) F d =
        globalSmul a.det F ≫ fractionHom g F d := by
  refine ⟨mixedFractionHom_difSucc (mixedEquations f g) a F
      (f := f) (mixedEquations_eq_dot f g a hg), ?_, ?_⟩
  · rw [← Category.assoc, mixedFractionHom_subfamilyProd_castAdd,
      fractionHom_prodTermCongr]
  · rw [← Category.assoc, mixedFractionHom_subfamilyProd_natAdd, Category.assoc,
      fractionHom_prodTermCongr]

/-- **Stacks Project, Tag 0G7S**, read on the classes of Stacks 0G7Q.

The class map `c_{f₁,…,f_c}` of Stacks 0G7Q is `supportedFractionClass f F`, carrying the class
of a local section `s` to the class of `s / (f₁ ⋯ f_c)` in the cokernel of the last differential
of the extended alternating Čech complex of `f₁, …, f_c`.  Both `c_{f₁,…,f_c}` and
`det(a_{ji}) c_{g₁,…,g_c}` are the image of the single degree-`c` class `σ` of the mixed complex
under the two projections.  This is the equality in the form the source proves it, with the two
sides still living in the cokernels of the last differentials of the `f`- and the `g`-complex
rather than in a common `i_*ℋ^c_Z(ℱ)`; the identification of those two cokernels with
`i_*ℋ^c_Z(ℱ)` is Stacks 0G7M, and composing it with this statement to obtain the single
equation is `supportedFractionClass_eq_det_smul` below. -/
@[stacks 0G7S "the same identity read on the two class maps c_{f₁,…,f_c} and c_{g₁,…,g_c} of
Stacks 0G7Q, with the two sides in the cokernels of the last differentials of the two complexes
rather than in a common i_*ℋ^c_Z(ℱ); the identification of those cokernels with i_*ℋ^c_Z(ℱ) is
Stacks 0G7M, and composing it with this statement to obtain the single equation is
supportedFractionClass_eq_det_smul in this module"]
public theorem mixedFractionHom_comp_cokernelπ (hg : ∀ j, g j = ∑ i, a j i * f i) :
    mixedFractionHom (mixedEquations f g) a F ≫
          subfamilyProd (mixedEquations f g) (Fin.castAddOrderEmb (d + 1) :
            Fin (d + 1) ↪o Fin ((d + 1) + (d + 1))) F d ≫
          prodTermCongr (mixedEquations_comp_castAdd f g) F d ≫
          cokernel.π (lastDif f F) =
        cokernel.π (equationsMultiplication f F) ≫ supportedFractionClass f F ∧
      mixedFractionHom (mixedEquations f g) a F ≫
          subfamilyProd (mixedEquations f g) (Fin.natAddOrderEmb (d + 1) :
            Fin (d + 1) ↪o Fin ((d + 1) + (d + 1))) F d ≫
          prodTermCongr (mixedEquations_comp_natAdd f g) F d ≫
          cokernel.π (lastDif g F) =
        globalSmul a.det F ≫
          cokernel.π (equationsMultiplication g F) ≫ supportedFractionClass g F := by
  obtain ⟨-, hf, hgg⟩ := mixedFractionHom_projections f g a F hg
  exact ⟨by rw [reassoc_of% hf, supportedFractionClass, cokernel.π_desc],
    by rw [reassoc_of% hgg, supportedFractionClass, cokernel.π_desc]⟩

end Main

/-! ### Cohomology classes of cocycles -/

section CocycleClass

/-- The class in degree-`i` homology of a morphism into the degree-`i` term whose composition
with the outgoing differential vanishes. -/
public def cocycleClass {K : CochainComplex X.Modules ℕ} {M : X.Modules} {i j : ℕ}
    (hj : (ComplexShape.up ℕ).next i = j) (u : M ⟶ K.X i) (hu : u ≫ K.d i j = 0)
    [K.HasHomology i] : M ⟶ K.homology i :=
  K.liftCycles u j hj hu ≫ K.homologyπ i

/-- The class of a cocycle is its lift to the cycles followed by the projection to the
homology. -/
public theorem cocycleClass_eq {K : CochainComplex X.Modules ℕ} {M : X.Modules} {i j : ℕ}
    (hj : (ComplexShape.up ℕ).next i = j) (u : M ⟶ K.X i) (hu : u ≫ K.d i j = 0)
    [K.HasHomology i] :
    cocycleClass hj u hu = K.liftCycles u j hj hu ≫ K.homologyπ i := rfl

/-- **The class of a cocycle depends only on the cocycle**, and not on the proof that it is one.
This is `cechCocycleClass_congr` below one level down, and it is what a caller needs when the two
cocycles are equal for a reason that cannot be rewritten under the cocycle condition: that
condition mentions the cocycle, so `rw` on it leaves a motive that is not type correct. -/
public theorem cocycleClass_congr {K : CochainComplex X.Modules ℕ} {M : X.Modules} {i j : ℕ}
    (hj : (ComplexShape.up ℕ).next i = j) {u u' : M ⟶ K.X i} (hu : u ≫ K.d i j = 0)
    (hu' : u' ≫ K.d i j = 0) (h : u = u') [K.HasHomology i] :
    cocycleClass hj u hu = cocycleClass hj u' hu' := by subst h; rfl

/-- Precomposing a cocycle precomposes its class. -/
public theorem comp_cocycleClass {K : CochainComplex X.Modules ℕ} {M N : X.Modules} {i j : ℕ}
    (hj : (ComplexShape.up ℕ).next i = j) (u : M ⟶ K.X i) (hu : u ≫ K.d i j = 0)
    [K.HasHomology i] (v : N ⟶ M) :
    v ≫ cocycleClass hj u hu =
      cocycleClass hj (v ≫ u) (by rw [Category.assoc, hu, comp_zero]) := by
  rw [cocycleClass, cocycleClass, ← Category.assoc, HomologicalComplex.comp_liftCycles]

/-- A morphism of complexes carries the class of a cocycle to the class of its image. -/
public theorem cocycleClass_comp_homologyMap {K L : CochainComplex X.Modules ℕ} (ψ : K ⟶ L)
    {M : X.Modules} {i j : ℕ} (hj : (ComplexShape.up ℕ).next i = j) (u : M ⟶ K.X i)
    (hu : u ≫ K.d i j = 0) [K.HasHomology i] [L.HasHomology i] :
    cocycleClass hj u hu ≫ HomologicalComplex.homologyMap ψ i =
      cocycleClass (K := L) hj (u ≫ ψ.f i)
        (by rw [Category.assoc, ψ.comm, ← Category.assoc, hu, zero_comp]) := by
  rw [cocycleClass, cocycleClass, Category.assoc, HomologicalComplex.homologyπ_naturality,
    ← Category.assoc]
  congr 1
  rw [← cancel_mono (L.iCycles i), Category.assoc, HomologicalComplex.cyclesMap_i,
    HomologicalComplex.liftCycles_i, ← Category.assoc, HomologicalComplex.liftCycles_i]

/-- The signed alternating differential out of a positive-degree term is the differential of the
extended alternating Čech complex. -/
public theorem comp_cplx_d_succ {m : ℕ} (e : Fin m → Γ(X, ⊤)) (F : X.Modules) (p : ℕ)
    {M : X.Modules} (u : M ⟶ prodTerm e F p) (hu : u ≫ difSucc e F p = 0) :
    u ≫ (cplx e F).d (p + 1) (p + 1 + 1) = 0 :=
  (congrArg (fun ψ : prodTerm e F p ⟶ prodTerm e F (p + 1) => u ≫ ψ)
    (cplx_d_succ e F p)).trans hu

/-- The degree-`(p + 1)` cohomology class of a degree-`(p + 1)` cocycle on the extended
alternating Čech complex. -/
public def cechCocycleClass {m : ℕ} (e : Fin m → Γ(X, ⊤)) (F : X.Modules) (p : ℕ)
    {M : X.Modules} (u : M ⟶ prodTerm e F p) (hu : u ≫ difSucc e F p = 0) :
    M ⟶ (cplx e F).homology (p + 1) :=
  cocycleClass (K := cplx e F) (CochainComplex.next ℕ (p + 1)) u (comp_cplx_d_succ e F p u hu)

/-- The class of a Čech cocycle depends only on the cocycle. -/
public theorem cechCocycleClass_congr {m : ℕ} (e : Fin m → Γ(X, ⊤)) (F : X.Modules) (p : ℕ)
    {M : X.Modules} {u u' : M ⟶ prodTerm e F p} (hu : u ≫ difSucc e F p = 0)
    (hu' : u' ≫ difSucc e F p = 0) (h : u = u') :
    cechCocycleClass e F p u hu = cechCocycleClass e F p u' hu' := by subst h; rfl

/-- Precomposing a Čech cocycle precomposes its class. -/
public theorem comp_cechCocycleClass {m : ℕ} (e : Fin m → Γ(X, ⊤)) (F : X.Modules) (p : ℕ)
    {M N : X.Modules} (u : M ⟶ prodTerm e F p) (hu : u ≫ difSucc e F p = 0) (v : N ⟶ M) :
    v ≫ cechCocycleClass e F p u hu =
      cechCocycleClass e F p (v ≫ u) (by rw [Category.assoc, hu, comp_zero]) :=
  comp_cocycleClass _ _ _ v

/-- The subfamily projection carries the class of a Čech cocycle to the class of its
projection. -/
public theorem cechCocycleClass_comp_homologyMap {m n : ℕ} (e : Fin n → Γ(X, ⊤))
    (φ : Fin m ↪o Fin n) (F : X.Modules) (p : ℕ) {M : X.Modules} (u : M ⟶ prodTerm e F p)
    (hu : u ≫ difSucc e F p = 0) :
    cechCocycleClass e F p u hu ≫
        HomologicalComplex.homologyMap (subfamilyCplxMap e φ F) (p + 1) =
      cechCocycleClass (e ∘ φ) F p (u ≫ subfamilyProd e φ F p)
        (by rw [Category.assoc, ← difSucc_subfamilyProd, ← Category.assoc, hu, zero_comp]) :=
  cocycleClass_comp_homologyMap _ _ _ _

end CocycleClass

/-! ### The cokernel of the last differential is the degree-`c` cohomology -/

section TopDegree

variable {d : ℕ} (f : Fin (d + 1) → Γ(X, ⊤)) (F : X.Modules)

/-- Beyond the top degree the extended alternating Čech complex has no components: an increasing
`(c + 1)`-tuple of `c` indices does not exist, so the differential out of the top degree is
zero. -/
public theorem difSucc_top_eq_zero : difSucc f F d = 0 := by
  have hempty : IsEmpty (CechCochains.OrdIndex (I := Fin (d + 1)) (d + 1)) := by
    refine ⟨fun q => ?_⟩
    have h := Fintype.card_le_of_injective q.1 q.2.injective
    simp only [Fintype.card_fin] at h
    omega
  exact Pi.hom_ext _ _ fun t => hempty.elim t

/-- Every morphism into the top-degree term is a cocycle. -/
public theorem comp_difSucc_top {M : X.Modules} (u : M ⟶ prodTerm f F d) :
    u ≫ difSucc f F d = 0 := by rw [difSucc_top_eq_zero, comp_zero]

/-- The differential out of the top degree of the extended alternating Čech complex is zero. -/
public theorem cplx_d_top_eq_zero : (cplx f F).d (d + 1) (d + 1 + 1) = 0 :=
  (cplx_d_succ f F d).trans (difSucc_top_eq_zero f F)

/-- In the top degree every section is a cycle: the top-degree term is the cycles. -/
public def topCyclesIso : prodTerm f F d ≅ (cplx f F).cycles (d + 1) :=
  ((cplx f F).iCyclesIso (d + 1) (d + 1 + 1) (CochainComplex.next ℕ (d + 1))
    (cplx_d_top_eq_zero f F)).symm

/-- The identification of the top-degree term with the cycles is inverse to the inclusion of the
cycles. -/
public theorem topCyclesIso_hom_iCycles :
    (topCyclesIso f F).hom ≫ (cplx f F).iCycles (d + 1) = 𝟙 (prodTerm f F d) :=
  HomologicalComplex.iCyclesIso_inv_hom_id (cplx f F) (d + 1) (d + 1 + 1)
    (CochainComplex.next ℕ (d + 1)) (cplx_d_top_eq_zero f F)

/-- Under the identification of the top-degree term with the cycles, the map to the cycles
induced by the last differential is the last differential. -/
public theorem toCycles_eq_lastDif_comp :
    (cplx f F).toCycles d (d + 1) = lastDif f F ≫ (topCyclesIso f F).hom :=
  (cancel_mono ((cplx f F).iCycles (d + 1))).mp
    ((((cplx f F).toCycles_i d (d + 1)).trans
      ((cplx_d_lastDif f F).trans
        ((Category.comp_id (lastDif f F)).symm.trans
          (congrArg (fun ψ : prodTerm f F d ⟶ prodTerm f F d => lastDif f F ≫ ψ)
            (topCyclesIso_hom_iCycles f F).symm)))).trans
      (Category.assoc (lastDif f F) (topCyclesIso f F).hom
        ((cplx f F).iCycles (d + 1))).symm)

/-- The lift of a top-degree cocycle to the cycles is the cocycle itself. -/
public theorem liftCycles_eq_comp_topCyclesIso {M : X.Modules} (u : M ⟶ prodTerm f F d) :
    (cplx f F).liftCycles u (d + 1 + 1) (CochainComplex.next ℕ (d + 1))
        (comp_cplx_d_succ f F d u (comp_difSucc_top f F u)) =
      u ≫ (topCyclesIso f F).hom :=
  (cancel_mono ((cplx f F).iCycles (d + 1))).mp
    ((HomologicalComplex.liftCycles_i (cplx f F) u (d + 1 + 1)
        (CochainComplex.next ℕ (d + 1))
        (comp_cplx_d_succ f F d u (comp_difSucc_top f F u))).trans
      (((Category.comp_id u).symm.trans
        (congrArg (fun ψ : prodTerm f F d ⟶ prodTerm f F d => u ≫ ψ)
          (topCyclesIso_hom_iCycles f F).symm)).trans
        (Category.assoc u (topCyclesIso f F).hom ((cplx f F).iCycles (d + 1))).symm))

/-- **The cokernel of the last differential is the degree-`c` cohomology of the extended
alternating Čech complex.** This is the first of the two identifications that Stacks 0G7Q and
Stacks 0G7M use to read the class `c_{f₁,…,f_c}` in `i_*ℋ^c_Z(ℱ)`: the complex has nothing above
degree `c`, so the top-degree term is its own cycles and the degree-`c` homology is the cokernel
of the last differential.  Both presentations are cokernels of the last differential, so the
identification is canonical. -/
public def cokernelLastDifIsoHomology : cokernel (lastDif f F) ≅ (cplx f F).homology (d + 1) :=
  CokernelCofork.mapIsoOfIsColimit (cokernelIsCokernel (lastDif f F))
    ((cplx f F).homologyIsCokernel d (d + 1) (CochainComplex.prev_nat_succ d))
    (Arrow.isoMk (Iso.refl _) (topCyclesIso f F)
      ((Category.id_comp _).trans (toCycles_eq_lastDif_comp f F)))

/-- The identification of the cokernel of the last differential with the degree-`c` cohomology
carries the class of a top-degree cochain to its cohomology class. -/
public theorem cokernelπ_comp_cokernelLastDifIsoHomology :
    cokernel.π (lastDif f F) ≫ (cokernelLastDifIsoHomology f F).hom =
      (topCyclesIso f F).hom ≫ (cplx f F).homologyπ (d + 1) :=
  CokernelCofork.π_mapOfIsColimit (cokernelIsCokernel (lastDif f F)) _ _

/-- The class in the cokernel of the last differential of the image of a morphism is its
degree-`c` cohomology class. -/
public theorem comp_cokernelπ_comp_cokernelLastDifIsoHomology {M : X.Modules}
    (u : M ⟶ prodTerm f F d) :
    u ≫ cokernel.π (lastDif f F) ≫ (cokernelLastDifIsoHomology f F).hom =
      cechCocycleClass f F d u (comp_difSucc_top f F u) :=
  (congrArg (fun ψ : prodTerm f F d ⟶ (cplx f F).homology (d + 1) => u ≫ ψ)
    (cokernelπ_comp_cokernelLastDifIsoHomology f F)).trans
    ((Category.assoc u (topCyclesIso f F).hom ((cplx f F).homologyπ (d + 1))).symm.trans
      (congrArg (fun ψ : M ⟶ (cplx f F).cycles (d + 1) => ψ ≫ (cplx f F).homologyπ (d + 1))
        (liftCycles_eq_comp_topCyclesIso f F u).symm))

end TopDegree

end Stacks.Perfect.SupportedFraction

end
