module

public import Mathlib.CategoryTheory.Sites.SheafCohomology.Basic
public import Mathlib.FieldTheory.IsAlgClosed.Basic
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.MultiplicativeSheaf
public import StacksFrontier.AlgebraicGeometry.GroupScheme.Examples.RootsOfUnity
public import StacksFrontier.AlgebraicGeometry.Topologies.Etale.Limits

/-!
# Degree-zero étale cohomology of roots of unity

On an integral scheme over an algebraically closed field, every global root of unity is
constant. Thus degree-zero étale cohomology with roots-of-unity coefficients is canonically
identified with the roots of unity of the field.

## Main definitions

* `AlgebraicGeometry.etaleH0EquivRootsOfUnitySections` identifies degree-zero cohomology
  with the roots of unity in global functions.
* `AlgebraicGeometry.baseRootsToEtaleH0` is the canonical map induced by the structure
  morphism to the base field.

## Main results

* `AlgebraicGeometry.rootsOfUnitySections_bijective_of_isIntegral` says all global roots of
  unity are constant.
* `AlgebraicGeometry.baseRootsToEtaleH0_bijective_of_isIntegral` gives the degree-zero
  identification.
* `AlgebraicGeometry.etaleH0EquivRootsOfUnitySections_val` characterizes the comparison by
  evaluation.

## Implementation notes

Degree-zero cohomology evaluates the roots-of-unity sheaf at the terminal object of the
small étale site. That sheaf is the kernel of the `n`-th power map on the sheaf of units, and
evaluation at the terminal object preserves this kernel, so its sections are the roots of
unity in the ring of global functions. Integrality of the scheme suffices for the comparison
to be bijective; affineness, smoothness, dimension one, and invertibility of `n` are
unnecessary here.

## References

* [Stacks Project, Tag 03RR](https://stacks.math.columbia.edu/tag/03RR)
-/

@[expose] public section

open CategoryTheory

universe u w

namespace AlgebraicGeometry

/-- Over an algebraically closed field, a root of unity in a domain algebra is the image of
a root of unity of the field: the polynomial `X ^ n - 1` splits, so one of its linear factors
vanishes at the given element. -/
private theorem exists_algebraMap_eq_of_pow_eq_one
    (k R : Type u) [Field k] [IsAlgClosed k] [CommRing R] [IsDomain R]
    [Algebra k R] (x : R) (n : ℕ) (hn : 0 < n) (hx : x ^ n = 1) :
    ∃ a : k, algebraMap k R a = x := by
  let p : Polynomial k := Polynomial.X ^ n - 1
  have hmonic : p.Monic := Polynomial.monic_X_pow_sub_C 1 hn.ne'
  have heval : Polynomial.aeval x p = 0 := by simp [p, hx]
  rw [(IsAlgClosed.splits p).eq_prod_roots_of_monic hmonic] at heval
  have hzero : (p.roots.map fun a : k => x - algebraMap k R a).prod = 0 := by
    simpa [Polynomial.aeval_def, Polynomial.eval₂_multiset_prod, p] using heval
  obtain ⟨a, -, hya⟩ := Multiset.mem_map.mp (Multiset.prod_eq_zero_iff.mp hzero)
  exact ⟨a, (sub_eq_zero.mp hya).symm⟩

/-- The kernel of the `n`-fold multiple of the identity on the additive form of an abelian
group is the subgroup of `n`-th roots of unity of the group. -/
def rootsOfUnityPowerKernelEquiv (A : Type u) [CommGroup A] (n : ℕ) :
    (AddMonoidHom.ker (n • (AddMonoidHom.id (Additive A)))) ≃
      {x : A // x ^ n = 1} where
  toFun x := ⟨Additive.toMul x.1, by
    simpa [toMul_nsmul] using congrArg Additive.toMul (show n • x.1 = 0 from x.2)⟩
  invFun x := ⟨Additive.ofMul x.1, by
    change n • Additive.ofMul x.1 = 0
    apply Additive.toMul.injective
    simpa [toMul_nsmul] using x.2⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- Sections of the roots-of-unity sheaf at the final object of the small étale site are the
roots of unity in global functions on the base: evaluation at the final object preserves the
kernel defining the sheaf. -/
noncomputable def rootsSheafSectionsEquiv
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (n : ℕ)
    [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat.{u}] :
    (rootsOfUnitySheaf (SmallEtale.topology B X hX)
      (SmallEtale.toScheme B X hX)
      (unitsPresheaf_isSheaf_smallEtale B X hX) n).obj.obj
      (Opposite.op (SmallEtale.final B X hX)) ≃
      (rootsOfUnitySections n).obj (Opposite.op X) := by
  let J := SmallEtale.topology B X hX
  let T := SmallEtale.final B X hX
  let F := unitsSheaf J (SmallEtale.toScheme B X hX)
    (unitsPresheaf_isSheaf_smallEtale B X hX)
  let p := powerSheaf J (SmallEtale.toScheme B X hX)
    (unitsPresheaf_isSheaf_smallEtale B X hX) n
  let K := Limits.kernel p
  let E : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf J AddCommGrpCat ⋙ (evaluation _ _).obj (Opposite.op T)
  let : Limits.PreservesLimit (Limits.parallelPair p 0) E := inferInstance
  have hp : E.map p = n • 𝟙 (E.obj F) := by
    apply AddCommGrpCat.hom_ext
    ext x
    rfl
  let e := (Limits.PreservesKernel.iso E p).trans <|
    (Limits.kernelIsoOfEq hp).trans
      (AddCommGrpCat.kernelIsoKer (n • 𝟙 (E.obj F)))
  have eK : E.obj K ≅
      AddCommGrpCat.of
        (AddMonoidHom.ker (n • (AddMonoidHom.id
          (Additive ((Scheme.Γ.obj (Opposite.op X))ˣ))))) := e
  change E.obj K ≃ _
  exact (CategoryTheory.Iso.addCommGroupIsoToAddEquiv eK).toEquiv.trans <|
    rootsOfUnityPowerKernelEquiv (Scheme.Γ.obj (Opposite.op X))ˣ n

/-- The identification of sections of the roots-of-unity sheaf is given by the inclusion of
the kernel into the sheaf of units. -/
theorem rootsSheafSectionsEquiv_val
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X) (n : ℕ)
    [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat.{u}]
    (z : (rootsOfUnitySheaf (SmallEtale.topology B X hX)
      (SmallEtale.toScheme B X hX)
      (unitsPresheaf_isSheaf_smallEtale B X hX) n).obj.obj
      (Opposite.op (SmallEtale.final B X hX))) :
    (rootsSheafSectionsEquiv B X hX n z).1 =
      Additive.toMul ((Limits.kernel.ι
        (powerSheaf (SmallEtale.topology B X hX)
          (SmallEtale.toScheme B X hX)
          (unitsPresheaf_isSheaf_smallEtale B X hX) n)).hom.app
        (Opposite.op (SmallEtale.final B X hX)) z) := by
  let J := SmallEtale.topology B X hX
  let T := SmallEtale.final B X hX
  let F := unitsSheaf J (SmallEtale.toScheme B X hX)
    (unitsPresheaf_isSheaf_smallEtale B X hX)
  let p := powerSheaf J (SmallEtale.toScheme B X hX)
    (unitsPresheaf_isSheaf_smallEtale B X hX) n
  let K := Limits.kernel p
  let E : Sheaf J AddCommGrpCat.{u} ⥤ AddCommGrpCat.{u} :=
    sheafToPresheaf J AddCommGrpCat ⋙ (evaluation _ _).obj (Opposite.op T)
  let : Limits.PreservesLimit (Limits.parallelPair p 0) E := inferInstance
  have hp : E.map p = n • 𝟙 (E.obj F) := by
    apply AddCommGrpCat.hom_ext
    ext x
    rfl
  let e := (Limits.PreservesKernel.iso E p).trans <|
    (Limits.kernelIsoOfEq hp).trans
      (AddCommGrpCat.kernelIsoKer (n • 𝟙 (E.obj F)))
  have he : e.hom ≫ AddCommGrpCat.ofHom
      (AddSubgroup.subtype (n • 𝟙 (E.obj F)).hom.ker) =
        (Limits.kernel.ι p).hom.app (Opposite.op T) := by
    dsimp [e]
    simp only [Category.assoc]
    rw [AddCommGrpCat.kernelIsoKer_hom_comp_subtype, Limits.kernelIsoOfEq_hom_comp_ι,
      Limits.PreservesKernel.iso_hom]
    simpa [E] using Limits.kernelComparison_comp_ι p E
  have hz := congrArg (fun g : AddCommGrpCat.Hom _ _ => g.hom z) he
  have hroot : (rootsSheafSectionsEquiv B X hX n z).1 =
      Additive.toMul (e.hom.hom z).1 := by
    simp only [rootsSheafSectionsEquiv]
    dsimp only [rootsOfUnityPowerKernelEquiv]
    change Additive.toMul (e.hom.hom z).1 = _
    rfl
  rw [hroot]
  exact congrArg Additive.toMul hz

/-- The canonical degree-zero comparison, from evaluation at the final étale object
and the kernel description of the roots-of-unity sheaf. -/
noncomputable def etaleH0EquivRootsOfUnitySections
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (n : ℕ)
    [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})] :
    Sheaf.H.{w, u}
      (rootsOfUnitySheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX)
        (unitsPresheaf_isSheaf_smallEtale B X hX) n) 0 ≃
      (rootsOfUnitySections n).obj (Opposite.op X) :=
  (Sheaf.H.equiv₀ _ (SmallEtale.finalIsTerminal B X hX)).toEquiv.trans
    (rootsSheafSectionsEquiv B X hX n)

/-- The comparison is the canonical evaluation of degree-zero cohomology at the final
étale object, followed by the inclusion of the kernel into the units sheaf. -/
@[stacks 03RR "degree_zero"]
theorem etaleH0EquivRootsOfUnitySections_val
    (B : BigEtaleSite.{u}) (X : Scheme.{u}) (hX : B.Contains X)
    (n : ℕ)
    [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})]
    (x : Sheaf.H.{w, u}
      (rootsOfUnitySheaf (SmallEtale.topology B X hX)
        (SmallEtale.toScheme B X hX)
        (unitsPresheaf_isSheaf_smallEtale B X hX) n) 0) :
    (etaleH0EquivRootsOfUnitySections B X hX n x).1 =
      Additive.toMul
        ((Limits.kernel.ι
          (powerSheaf (SmallEtale.topology B X hX)
            (SmallEtale.toScheme B X hX)
            (unitsPresheaf_isSheaf_smallEtale B X hX) n)).hom.app
          (Opposite.op (SmallEtale.final B X hX))
          ((Sheaf.H.equiv₀
            (rootsOfUnitySheaf (SmallEtale.topology B X hX)
              (SmallEtale.toScheme B X hX)
              (unitsPresheaf_isSheaf_smallEtale B X hX) n)
            (SmallEtale.finalIsTerminal B X hX)) x)) :=
  rootsSheafSectionsEquiv_val B X hX n _

/-- Pullback of a constant root followed by the degree-zero comparison. -/
noncomputable def baseRootsToEtaleH0
    (B : BigEtaleSite.{u}) (k : Type u) [Field k]
    (X : Scheme.{u}) (hX : B.Contains X) (f : X ⟶ Spec (.of k)) (n : ℕ)
    [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})] :
    (rootsOfUnitySections n).obj
      (Opposite.op (Spec (.of k))) →
      Sheaf.H.{w, u}
        (rootsOfUnitySheaf (SmallEtale.topology B X hX)
          (SmallEtale.toScheme B X hX)
          (unitsPresheaf_isSheaf_smallEtale B X hX) n) 0 :=
  (etaleH0EquivRootsOfUnitySections B X hX n).symm ∘
    (rootsOfUnitySections n).map f.op

/-- Roots of unity in global sections of an integral scheme over an algebraically
closed field are precisely the constants. -/
@[stacks 03RR "degree_zero"]
theorem rootsOfUnitySections_bijective_of_isIntegral
    (k : Type u) [Field k] [IsAlgClosed k]
    {X : Scheme.{u}} [IsIntegral X] (f : X ⟶ Spec (.of k))
    (n : ℕ) (hn : 0 < n) :
    Function.Bijective
      ((rootsOfUnitySections n).map f.op) := by
  have : IsDomain (Scheme.Γ.obj (Opposite.op X)) := inferInstanceAs (IsDomain Γ(X, ⊤))
  let φ : k →+* Scheme.Γ.obj (Opposite.op X) :=
    ((Scheme.ΓSpecIso (.of k)).inv ≫ Scheme.Γ.map f.op).hom
  let : Algebra k (Scheme.Γ.obj (Opposite.op X)) := φ.toAlgebra
  have hφ : Function.Injective φ := RingHom.injective φ
  have hΓ : Function.Injective (Scheme.ΓSpecIso (.of k)).hom.hom :=
    (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (.of k)).hom).injective
  have hfactor (z : Scheme.Γ.obj (Opposite.op (Spec (.of k)))) :
      φ ((Scheme.ΓSpecIso (.of k)).hom.hom z) = (Scheme.Γ.map f.op).hom z := by
    have hz : (Scheme.ΓSpecIso (.of k)).inv.hom
        ((Scheme.ΓSpecIso (.of k)).hom.hom z) = z :=
      congrArg (fun g : CommRingCat.Hom _ _ => g.hom z) (Scheme.ΓSpecIso (.of k)).hom_inv_id
    change (Scheme.Γ.map f.op).hom
        ((Scheme.ΓSpecIso (.of k)).inv.hom ((Scheme.ΓSpecIso (.of k)).hom.hom z)) = _
    exact congrArg (Scheme.Γ.map f.op).hom hz
  have hψ : Function.Injective (Scheme.Γ.map f.op).hom := fun a b hab =>
    hΓ (hφ (by rwa [hfactor, hfactor]))
  refine ⟨fun a b hab => Subtype.ext (Units.map_injective hψ (congrArg Subtype.val hab)), ?_⟩
  rintro ⟨x, hx⟩
  have hxpow : x.val ^ n = 1 := congrArg Units.val hx
  obtain ⟨a, ha⟩ : ∃ a : k, φ a = x.val :=
    exists_algebraMap_eq_of_pow_eq_one k (Scheme.Γ.obj (Opposite.op X)) x.val n hn hxpow
  have hapow : a ^ n = 1 := hφ (by rw [map_pow, ha, hxpow, map_one])
  let y : (Scheme.Γ.obj (Opposite.op (Spec (.of k))))ˣ :=
    Units.map (Scheme.ΓSpecIso (.of k)).inv.hom.toMonoidHom (Units.ofPowEqOne a n hapow hn.ne')
  have hypow : y ^ n = 1 := by
    apply Units.ext
    change ((Scheme.ΓSpecIso (.of k)).inv.hom a) ^ n = 1
    rw [← map_pow, hapow, map_one]
  exact ⟨⟨y, hypow⟩, Subtype.ext (Units.ext ha)⟩

/-- The canonical pullback from the field's roots of unity to degree-zero étale
cohomology is bijective over an algebraically closed field. -/
@[stacks 03RR "degree_zero"]
theorem baseRootsToEtaleH0_bijective_of_isIntegral
    (B : BigEtaleSite.{u}) (k : Type u) [Field k] [IsAlgClosed k]
    (X : Scheme.{u}) [IsIntegral X] (hX : B.Contains X)
    (f : X ⟶ Spec (.of k)) (n : ℕ) (hn : 0 < n)
    [HasSheafify (SmallEtale.topology B X hX) AddCommGrpCat.{u}]
    [HasExt.{w} (Sheaf (SmallEtale.topology B X hX) AddCommGrpCat.{u})] :
    Function.Bijective (baseRootsToEtaleH0 B k X hX f n) :=
  (etaleH0EquivRootsOfUnitySections B X hX n).symm.bijective.comp
    (rootsOfUnitySections_bijective_of_isIntegral k f n hn)

end AlgebraicGeometry

end
