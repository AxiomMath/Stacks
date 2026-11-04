module

public import Mathlib.AlgebraicGeometry.AffineScheme
public import Mathlib.AlgebraicGeometry.Limits
public import StacksFrontier.Topology.Sheaves.Basis.OnBasis
public import StacksFrontier.AlgebraicGeometry.Scheme.Zariski.StandardOpenCover
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Topology.Dimension.CounterexampleCodimension

/-!
# Sheaves on the affine-open basis of a scheme

The affine opens of a scheme form a basis of its topology, so a sheaf on a scheme is determined
by its sections over affine opens. This file characterises, among the presheaves of sets defined
only on that basis, those that arise this way: a presheaf on the affine-open basis is the
restriction of a sheaf precisely when it satisfies the sheaf condition on the basis.

That condition is in turn tested on very few covers. It suffices to know that the presheaf has a
single section over the empty open, and that over every affine open `U` presented as the union
of two standard opens `D(f) ∪ D(g)`, a pair of sections agreeing on `D(fg)` glues to a unique
section over `U`.

## Main definitions

* `AlgebraicGeometry.Scheme.affineBasisOpen`: an affine open of `X`, regarded as an object of the
  basis category on which presheaves on the affine-open basis are defined.

## Main results

* `AlgebraicGeometry.Scheme.isRestriction_iff_isSheafOnAffineBasis`: a presheaf on the affine
  opens is isomorphic to the restriction of a sheaf on `X` if and only if it is a sheaf on the
  affine-open basis.
* `AlgebraicGeometry.Scheme.isSheafOnAffineBasis_iff_standardPairs`: being a sheaf on the
  affine-open basis is equivalent to the empty-open and standard-pair gluing conditions.

## Implementation notes

Restriction in the first result is understood up to isomorphism of presheaves, as is natural for
the equivalence between sheaves on a space and sheaves on a basis. The standard-pair condition is
expressed as unique gluing for a compatible pair, which is equivalent to injectivity of the
restriction map together with a characterisation of its image.

## References

* [Stacks Project, Tag 0F1A](https://stacks.math.columbia.edu/tag/0F1A)
-/

@[expose] public section

open CategoryTheory Opposite TopologicalSpace Stacks.OpensBasis

universe u v

namespace Stacks.OpensBasis

private lemma isSheafOnBasis_of_iso {X : TopCat.{u}} {B : Set (Opens X)}
    {F G : Stacks.OpensBasis.PresheafOnBasis B} (e : F ≅ G)
    (hG : Stacks.OpensBasis.IsSheafOnBasis B G) :
    Stacks.OpensBasis.IsSheafOnBasis B F := by
  refine ⟨?_, ?_⟩
  · intro U ι 𝒰 hcov s t hagree
    have hagree' : ∀ i, G.restrictMap B
        ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov)
        (e.hom.app (op U) s) =
        G.restrictMap B
        ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov)
        (e.hom.app (op U) t) := by
      intro i
      show G.map ((basisHom B ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov)).op)
          (e.hom.app (op U) s) =
        G.map ((basisHom B ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov)).op)
          (e.hom.app (op U) t)
      rw [← NatTrans.naturality_apply e.hom
        (basisHom B ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov)).op s]
      rw [← NatTrans.naturality_apply e.hom
        (basisHom B ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov)).op t]
      exact congrArg (e.hom.app (op (𝒰 i))) (hagree i)
    have hEq := hG.separated U 𝒰 hcov (e.hom.app (op U) s) (e.hom.app (op U) t) hagree'
    have hEq' := congrArg (e.inv.app (op U)) hEq
    simpa using hEq'
  · intro U ι 𝒰 hcov s hcompat
    have hcompat' : ∀ i j (V : Stacks.OpensBasis.BasisCat B)
        (hVi : V.obj ≤ (𝒰 i).obj) (hVj : V.obj ≤ (𝒰 j).obj),
        G.restrictMap B hVi (e.hom.app (op (𝒰 i)) (s i)) =
          G.restrictMap B hVj (e.hom.app (op (𝒰 j)) (s j)) := by
      intro i j V hVi hVj
      show G.map (basisHom B hVi).op (e.hom.app (op (𝒰 i)) (s i)) =
        G.map (basisHom B hVj).op (e.hom.app (op (𝒰 j)) (s j))
      rw [← NatTrans.naturality_apply e.hom (basisHom B hVi).op (s i)]
      rw [← NatTrans.naturality_apply e.hom (basisHom B hVj).op (s j)]
      exact congrArg (e.hom.app (op V)) (hcompat i j V hVi hVj)
    obtain ⟨t, ht⟩ := hG.glue U 𝒰 hcov (fun i => e.hom.app (op (𝒰 i)) (s i)) hcompat'
    let r : F.obj (op U) := e.inv.app (op U) t
    refine ⟨r, ?_⟩
    intro i
    have hnat := NatTrans.naturality_apply e.hom
      (basisHom B ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov)).op r
    have hleft : e.hom.app (op U) r = t := by
      simp [r]
    have hEq : e.hom.app (op (𝒰 i)) (F.restrictMap B
          ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov) r) =
          e.hom.app (op (𝒰 i)) (s i) := calc
      e.hom.app (op (𝒰 i)) (F.restrictMap B
          ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov) r) =
          G.restrictMap B ((le_iSup (fun j => ((𝒰 j).obj : Opens X)) i).trans_eq hcov)
            (e.hom.app (op U) r) := hnat
      _ = e.hom.app (op (𝒰 i)) (s i) := by rw [hleft, ht i]
    have hEq' := congrArg (e.inv.app (op (𝒰 i))) hEq
    simpa using hEq'

/-- The restriction map of a presheaf on a basis with values in an arbitrary universe,
along an inclusion of basis elements. -/
def basisRestrictMap {T : TopCat.{u}} (basis : Set (Opens T))
    (F : (BasisCat basis)ᵒᵖ ⥤ Type v) {U V : BasisCat basis} (h : V.obj ≤ U.obj)
    (s : F.obj (op U)) : F.obj (op V) :=
  F.map (basisHom basis h).op s

end Stacks.OpensBasis

namespace AlgebraicGeometry.Scheme

/-- Regard an affine open as an object of the affine-open basis category. -/
abbrev affineBasisOpen (X : Scheme.{u}) (U : X.affineOpens) :
    BasisCat X.affineOpens := ⟨U.1, U.2⟩

section Helpers

private lemma basicOpen_le_iSup_of_mem_span {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {f : Γ(X, U)} {s : Set Γ(X, U)}
    (hf : f ∈ Ideal.span s) :
    X.basicOpen f ≤ ⨆ g : s, X.basicOpen (g : Γ(X, U)) := by
  intro x hx
  have hxU : x ∈ U := (X.basicOpen_le f) hx
  let p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  have hfrom : hU.fromSpec p = x := by
    simpa [p] using hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hpre : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen f := by
    show hU.fromSpec p ∈ X.basicOpen f
    simpa [hfrom] using hx
  have hp : p ∈ PrimeSpectrum.basicOpen f := by
    rw [hU.fromSpec_preimage_basicOpen'] at hpre
    exact (basicOpen_eq_of_affine f) ▸ hpre
  have hp' : p ∈ ⨆ g : s, PrimeSpectrum.basicOpen (g : Γ(X, U)) := by
    by_contra hnot
    have hmem : Ideal.span s ≤ p.asIdeal := Ideal.span_le.2 (by
      intro g hg
      have hnotg : p ∉ PrimeSpectrum.basicOpen (g : Γ(X, U)) := by
        intro hpg
        exact hnot (Opens.mem_iSup.mpr ⟨⟨g, hg⟩, hpg⟩)
      by_contra hmem
      exact hnotg ((PrimeSpectrum.mem_basicOpen _ _).mpr hmem))
    exact (PrimeSpectrum.mem_basicOpen _ _).mp hp (hmem hf)
  obtain ⟨g, hg⟩ := Opens.mem_iSup.mp hp'
  apply Opens.mem_iSup.mpr ⟨g, ?_⟩
  have hmem : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen (g : Γ(X, U)) := by
    rwa [hU.fromSpec_preimage_basicOpen]
  change hU.fromSpec p ∈ X.basicOpen (g : Γ(X, U)) at hmem
  simpa [hfrom] using hmem

/-- Restricting a presheaf on the affine-open basis along two nested inclusions of affine
opens is restricting along the composite inclusion. -/
lemma basisRestrictMap_comp {X : Scheme.{u}} (F : (BasisCat X.affineOpens)ᵒᵖ ⥤ Type v)
    {A B C : BasisCat X.affineOpens} (hAB : B.obj ≤ A.obj) (hBC : C.obj ≤ B.obj)
    (s : F.obj (op A)) :
    basisRestrictMap X.affineOpens F hBC (basisRestrictMap X.affineOpens F hAB s) =
      basisRestrictMap X.affineOpens F (hBC.trans hAB) s := by
  show (F.map (basisHom X.affineOpens hAB).op ≫
      F.map (basisHom X.affineOpens hBC).op) s =
    F.map (basisHom X.affineOpens (hBC.trans hAB)).op s
  rw [← F.map_comp]
  congr 1

private lemma restrictMap_comp {X : Scheme.{u}} (F : PresheafOnBasis X.affineOpens)
    {A B C : BasisCat X.affineOpens} (hAB : B.obj ≤ A.obj) (hBC : C.obj ≤ B.obj)
    (s : F.obj (op A)) :
    F.restrictMap X.affineOpens hBC (F.restrictMap X.affineOpens hAB s) =
      F.restrictMap X.affineOpens (hBC.trans hAB) s :=
  basisRestrictMap_comp F hAB hBC s

private lemma mul_le_left {X : Scheme.{u}} {U : X.affineOpens} (f g : Γ(X, U.1)) :
    (affineBasisOpen X (X.affineBasicOpen (f * g))).obj ≤
      (affineBasisOpen X (X.affineBasicOpen f)).obj := by
  change X.basicOpen (f * g) ≤ X.basicOpen f
  rw [X.basicOpen_mul]
  exact inf_le_left

private lemma mul_le_right {X : Scheme.{u}} {U : X.affineOpens} (f g : Γ(X, U.1)) :
    (affineBasisOpen X (X.affineBasicOpen (f * g))).obj ≤
      (affineBasisOpen X (X.affineBasicOpen g)).obj := by
  change X.basicOpen (f * g) ≤ X.basicOpen g
  rw [X.basicOpen_mul]
  exact inf_le_right

private lemma iSup_basicOpen_res {X : Scheme.{u}} {U V : X.Opens} (hVU : V ≤ U) {ι : Type*}
    (f : ι → Γ(X, U)) (hV : V ≤ ⨆ i, X.basicOpen (f i)) :
    (⨆ i, X.basicOpen (X.presheaf.map (homOfLE hVU).op (f i))) = V := by
  simp only [X.basicOpen_res]
  rw [← inf_iSup_eq]
  exact inf_eq_left.2 hV

private lemma res_basicOpen_le {X : Scheme.{u}} {U V : X.affineOpens} (hVU : V.1 ≤ U.1)
    (f : Γ(X, U.1)) :
    (affineBasisOpen X (X.affineBasicOpen (X.presheaf.map (homOfLE hVU).op f))).obj ≤
      (affineBasisOpen X (X.affineBasicOpen f)).obj := by
  change X.basicOpen (X.presheaf.map _ f) ≤ X.basicOpen f
  rw [X.basicOpen_res]
  exact inf_le_right

/-- Restricting a compatible family of sections along the basic opens `D(f i)` to a smaller affine
open `V` gives a compatible family. -/
private lemma compat_res {X : Scheme.{u}} (F : (BasisCat X.affineOpens)ᵒᵖ ⥤ Type v)
    {U V : X.affineOpens} (hVU : V.1 ≤ U.1) {ι : Type*} (f : ι → Γ(X, U.1))
    (s : ∀ i, F.obj (op (affineBasisOpen X (X.affineBasicOpen (f i)))))
    (hcompat : ∀ i j,
      basisRestrictMap X.affineOpens F (mul_le_left (f i) (f j)) (s i) =
        basisRestrictMap X.affineOpens F (mul_le_right (f i) (f j)) (s j))
    (f' : ι → Γ(X, V.1))
    (hle : ∀ i, (affineBasisOpen X (X.affineBasicOpen (f' i))).obj ≤
      (affineBasisOpen X (X.affineBasicOpen (f i))).obj)
    (hf' : f' = fun i => X.presheaf.map (homOfLE hVU).op (f i)) (i j : ι) :
    basisRestrictMap X.affineOpens F (mul_le_left (f' i) (f' j))
        (basisRestrictMap X.affineOpens F (hle i) (s i)) =
      basisRestrictMap X.affineOpens F (mul_le_right (f' i) (f' j))
        (basisRestrictMap X.affineOpens F (hle j) (s j)) := by
  subst hf'
  have hProd : (affineBasisOpen X (X.affineBasicOpen
      (X.presheaf.map (homOfLE hVU).op (f i) * X.presheaf.map (homOfLE hVU).op (f j)))).obj ≤
      (affineBasisOpen X (X.affineBasicOpen (f i * f j))).obj := by
    change X.basicOpen (X.presheaf.map (homOfLE hVU).op (f i) *
      X.presheaf.map (homOfLE hVU).op (f j)) ≤ X.basicOpen (f i * f j)
    simp only [X.basicOpen_mul, X.basicOpen_res]
    exact inf_le_inf inf_le_right inf_le_right
  have := congrArg (basisRestrictMap X.affineOpens F hProd) (hcompat i j)
  simpa only [basisRestrictMap_comp] using this

/-- The restrictions of a single section to the basic opens `D(f i)` are compatible. -/
private lemma compat_single {X : Scheme.{u}} (F : (BasisCat X.affineOpens)ᵒᵖ ⥤ Type v)
    {U : X.affineOpens} {A : BasisCat X.affineOpens} {ι : Type*} (f : ι → Γ(X, U.1))
    (h : ∀ i, (affineBasisOpen X (X.affineBasicOpen (f i))).obj ≤ A.obj) (a : F.obj (op A))
    (i j : ι) :
    basisRestrictMap X.affineOpens F (mul_le_left (f i) (f j))
        (basisRestrictMap X.affineOpens F (h i) a) =
      basisRestrictMap X.affineOpens F (mul_le_right (f i) (f j))
        (basisRestrictMap X.affineOpens F (h j) a) := by
  simp only [basisRestrictMap_comp]

private def StandardPairProperty (X : Scheme.{u}) (F : PresheafOnBasis X.affineOpens) : Prop :=
      ∀ (U : X.affineOpens) (f g : Γ(X, U.1))
        (_hcov : U.1 = X.basicOpen f ⊔ X.basicOpen g)
        (s : F.obj (op (affineBasisOpen X (X.affineBasicOpen f))))
        (t : F.obj (op (affineBasisOpen X (X.affineBasicOpen g)))),
        (F.restrictMap X.affineOpens
            (show (affineBasisOpen X (X.affineBasicOpen (f * g))).obj ≤
                (affineBasisOpen X (X.affineBasicOpen f)).obj by
              change X.basicOpen (f * g) ≤ X.basicOpen f
              rw [X.basicOpen_mul]
              exact inf_le_left) s =
          F.restrictMap X.affineOpens
            (show (affineBasisOpen X (X.affineBasicOpen (f * g))).obj ≤
                (affineBasisOpen X (X.affineBasicOpen g)).obj by
              change X.basicOpen (f * g) ≤ X.basicOpen g
              rw [X.basicOpen_mul]
              exact inf_le_right) t) →
        ∃! r : F.obj (op (affineBasisOpen X U)),
          (F.restrictMap X.affineOpens (by exact (X.affineBasicOpen_le f)) r = s) ∧
          (F.restrictMap X.affineOpens (by exact (X.affineBasicOpen_le g)) r = t)

private lemma isSheafOnBasis_imp_emptyAndPairs (X : Scheme.{u})
    (F : PresheafOnBasis X.affineOpens)
    (hF : IsSheafOnBasis X.affineOpens F) :
    (∃! _s : F.obj (op (affineBasisOpen X ⟨⊥, isAffineOpen_bot X⟩)), True) ∧
      StandardPairProperty X F := by
  constructor
  · let E := affineBasisOpen X ⟨⊥, isAffineOpen_bot X⟩
    let C : ULift.{u} Empty → BasisCat X.affineOpens := fun i => Empty.elim i.down
    have hcov : (⨆ i : ULift.{u} Empty, (C i).obj) = E.obj := by
      simp [E]
    have sec : ∀ i : ULift.{u} Empty, F.obj (op (C i)) := fun i => Empty.elim i.down
    have hcompat : ∀ i j (V : BasisCat X.affineOpens)
        (hVi : V.obj ≤ (C i).obj) (hVj : V.obj ≤ (C j).obj),
        F.restrictMap X.affineOpens hVi (sec i) =
      F.restrictMap X.affineOpens hVj (sec j) := by
      intro i
      exact Empty.elim i.down
    obtain ⟨t, _⟩ := hF.glue (ι := ULift.{u} Empty) E C hcov sec hcompat
    refine ⟨t, trivial, ?_⟩
    intro s _
    apply hF.separated E C hcov s t
    intro i
    exact Empty.elim i.down
  · intro U f g hcov s t hagree
    let A := affineBasisOpen X (X.affineBasicOpen f)
    let B := affineBasisOpen X (X.affineBasicOpen g)
    let W := affineBasisOpen X (X.affineBasicOpen (f * g))
    let C : ULift.{u} Bool → BasisCat X.affineOpens := fun b => Bool.rec A B b.down
    let sec : (b : ULift.{u} Bool) → F.obj (op (C b)) :=
      fun b => Bool.rec (motive := fun b => F.obj (op (C (ULift.up b)))) s t b.down
    have hcover : (⨆ b, (C b).obj) = (affineBasisOpen X U).obj := by
      apply le_antisymm
      · intro x hx
        obtain ⟨b, hb⟩ := Opens.mem_iSup.mp hx
        cases b with
        | up b =>
          cases b
          · change x ∈ X.basicOpen f at hb
            show x ∈ U.1
            exact (X.affineBasicOpen_le f) hb
          · change x ∈ X.basicOpen g at hb
            show x ∈ U.1
            exact (X.affineBasicOpen_le g) hb
      · intro x hx
        change x ∈ U.1 at hx
        rw [hcov] at hx
        rcases Opens.mem_sup.mp hx with hx | hx
        · refine Opens.mem_iSup.mpr ⟨ULift.up false, ?_⟩
          show x ∈ X.basicOpen f
          exact hx
        · refine Opens.mem_iSup.mpr ⟨ULift.up true, ?_⟩
          show x ∈ X.basicOpen g
          exact hx
    have key : ∀ (V : BasisCat X.affineOpens) (hVi : V.obj ≤ A.obj) (hVj : V.obj ≤ B.obj),
        F.restrictMap X.affineOpens hVi s = F.restrictMap X.affineOpens hVj t := by
      intro V hVi hVj
      have hVW : V.obj ≤ W.obj := by
        change V.obj ≤ X.basicOpen (f * g)
        rw [X.basicOpen_mul]
        exact le_inf hVi hVj
      have := congrArg (F.restrictMap X.affineOpens hVW) hagree
      simpa only [restrictMap_comp] using this
    have hcompat : ∀ i j (V : BasisCat X.affineOpens)
        (hVi : V.obj ≤ (C i).obj) (hVj : V.obj ≤ (C j).obj),
        F.restrictMap X.affineOpens hVi (sec i) =
          F.restrictMap X.affineOpens hVj (sec j) := by
      rintro ⟨_ | _⟩ ⟨_ | _⟩ V hVi hVj
      · rfl
      · exact key V hVi hVj
      · exact (key V hVj hVi).symm
      · rfl
    obtain ⟨r, hr⟩ := hF.glue (ι := ULift.{u} Bool)
      (affineBasisOpen X U) C hcover sec hcompat
    refine ⟨r, ?_, ?_⟩
    · constructor
      · simpa [C, sec] using hr (ULift.up false)
      · simpa [C, sec] using hr (ULift.up true)
    · intro r' hr'
      apply hF.separated (affineBasisOpen X U) C hcover r' r
      intro b
      cases b with
      | up b =>
        cases b
        · have hglue := hr (ULift.up false)
          convert hr'.1.trans hglue.symm using 1
        · have hglue := hr (ULift.up true)
          convert hr'.2.trans hglue.symm using 1

/-- Over an affine open `U` presented as a union `D(f) ∪ D(g)` of two standard opens, a
compatible pair of sections of a presheaf on the affine-open basis glues uniquely over `U`;
together with a single section over the empty open this forces unique gluing for every finite
family of standard opens covering `U`. -/
lemma finite_basicOpen_glue (X : Scheme.{u})
    (F : (BasisCat X.affineOpens)ᵒᵖ ⥤ Type v)
    (hempty : ∃! _s : F.obj (op (affineBasisOpen X ⟨⊥, isAffineOpen_bot X⟩)), True)
    (hpair : ∀ (U : X.affineOpens) (f g : Γ(X, U.1))
      (_hcov : U.1 = X.basicOpen f ⊔ X.basicOpen g)
      (s : F.obj (op (affineBasisOpen X (X.affineBasicOpen f))))
      (t : F.obj (op (affineBasisOpen X (X.affineBasicOpen g)))),
      basisRestrictMap X.affineOpens F
          (show (affineBasisOpen X (X.affineBasicOpen (f * g))).obj ≤
              (affineBasisOpen X (X.affineBasicOpen f)).obj by
            change X.basicOpen (f * g) ≤ X.basicOpen f
            rw [X.basicOpen_mul]
            exact inf_le_left) s =
        basisRestrictMap X.affineOpens F
          (show (affineBasisOpen X (X.affineBasicOpen (f * g))).obj ≤
              (affineBasisOpen X (X.affineBasicOpen g)).obj by
            change X.basicOpen (f * g) ≤ X.basicOpen g
            rw [X.basicOpen_mul]
            exact inf_le_right) t →
      ∃! r : F.obj (op (affineBasisOpen X U)),
        (basisRestrictMap X.affineOpens F (by exact (X.affineBasicOpen_le f)) r = s) ∧
        (basisRestrictMap X.affineOpens F (by exact (X.affineBasicOpen_le g)) r = t)) :
    ∀ (U : X.affineOpens) (n : ℕ) (f : Fin n → Γ(X, U.1))
      (_hcov : (⨆ i, X.basicOpen (f i)) = U.1)
      (s : ∀ i : Fin n, F.obj (op (affineBasisOpen X (X.affineBasicOpen (f i)))))
      (_hcompat : ∀ i j,
        basisRestrictMap X.affineOpens F
          (show (affineBasisOpen X (X.affineBasicOpen (f i * f j))).obj ≤
              (affineBasisOpen X (X.affineBasicOpen (f i))).obj by
            change X.basicOpen (f i * f j) ≤ X.basicOpen (f i)
            rw [X.basicOpen_mul]
            exact inf_le_left) (s i) =
        basisRestrictMap X.affineOpens F
          (show (affineBasisOpen X (X.affineBasicOpen (f i * f j))).obj ≤
              (affineBasisOpen X (X.affineBasicOpen (f j))).obj by
            change X.basicOpen (f i * f j) ≤ X.basicOpen (f j)
            rw [X.basicOpen_mul]
            exact inf_le_right) (s j)),
      (∃! r : F.obj (op (affineBasisOpen X U)),
        ∀ i, basisRestrictMap X.affineOpens F
          (X.affineBasicOpen_le (V := U) (f i)) r = s i) := by
  classical
  intro U n
  induction n generalizing U with
  | zero =>
      intro f hcov s hcompat
      have hU : U.1 = ⊥ := by simpa using hcov.symm
      have hEq : U = ⟨⊥, isAffineOpen_bot X⟩ := by
        apply Subtype.ext
        exact hU
      subst U
      obtain ⟨r, -, huniq⟩ := hempty
      refine ⟨r, ?_, ?_⟩
      · intro i
        exact Fin.elim0 i
      · intro r' hr'
        exact huniq r' trivial
  | succ n ih =>
      intro f hcov s hcompat
      have hspan : Ideal.span (Set.range f) = ⊤ := by
        apply (U.2.iSup_basicOpen_eq_self_iff (s := Set.range f)).mp
        simpa using hcov
      have hmem : (1 : Γ(X, U.1)) ∈ Ideal.span (Set.range f) := by
        rw [hspan]
        simp
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hmem
      let g : Γ(X, U.1) := ∑ i : Fin n, c i.succ * f i.succ
      have hdecomp : c 0 * f 0 + g = 1 := by
        have hc' : (∑ i : Fin (n + 1), c i * f i) = 1 := hc
        simpa [g, Fin.sum_univ_succ] using hc'
      have hgspan : g ∈ Ideal.span (Set.range (fun i : Fin n => f i.succ)) := by
        show (∑ i : Fin n, c i.succ * f i.succ) ∈
          Ideal.span (Set.range (fun i : Fin n => f i.succ))
        apply Submodule.sum_mem
        intro i hi
        exact Ideal.mul_mem_left _ _ (Ideal.subset_span ⟨i, rfl⟩)
      have hDg : X.basicOpen g ≤ ⨆ i : Fin n, X.basicOpen (f i.succ) := by
        simpa only [iSup_range'] using basicOpen_le_iSup_of_mem_span U.2 hgspan
      have hpairspan : Ideal.span ({f 0, g} : Set Γ(X, U.1)) = ⊤ := by
        apply (Ideal.eq_top_iff_one _).2
        rw [Ideal.mem_span_pair]
        exact ⟨c 0, 1, by simpa [g] using hdecomp⟩
      have hpaircov : U.1 = X.basicOpen (f 0) ⊔ X.basicOpen g := by
        have hcov' := (U.2.iSup_basicOpen_eq_self_iff
          (s := ({f 0, g} : Set Γ(X, U.1)))).2 hpairspan
        rw [iSup_subtype''] at hcov'
        rw [iSup_pair] at hcov'
        exact hcov'.symm
      let V := X.affineBasicOpen g
      have hVU : V.1 ≤ U.1 := X.affineBasicOpen_le g
      let f' : Fin n → Γ(X, V.1) := fun i =>
        X.presheaf.map (CategoryTheory.homOfLE hVU).op (f i.succ)
      let s' : ∀ i, F.obj (op (affineBasisOpen X (X.affineBasicOpen (f' i)))) := fun i =>
        basisRestrictMap X.affineOpens F (res_basicOpen_le hVU (f i.succ)) (s i.succ)
      have hcov' := iSup_basicOpen_res (V := X.basicOpen g) hVU (fun i : Fin n => f i.succ) hDg
      obtain ⟨t, ht, htu⟩ := ih V f' hcov' s' (compat_res F hVU (fun i : Fin n => f i.succ)
        (fun i => s i.succ) (fun i j => hcompat i.succ j.succ) f'
        (fun i => res_basicOpen_le hVU (f i.succ)) rfl)
      let W := X.affineBasicOpen (f 0 * g)
      have hWU : W.1 ≤ U.1 := X.affineBasicOpen_le (f 0 * g)
      have hWV : W.1 ≤ V.1 := mul_le_right (f 0) g
      let q : Fin n → Γ(X, W.1) := fun i =>
        X.presheaf.map (CategoryTheory.homOfLE hWU).op (f i.succ)
      let sq : ∀ i, F.obj (op (affineBasisOpen X (X.affineBasicOpen (q i)))) := fun i =>
        basisRestrictMap X.affineOpens F (res_basicOpen_le hWU (f i.succ)) (s i.succ)
      have hqcov := iSup_basicOpen_res (V := W.1) hWU (fun i : Fin n => f i.succ) (hWV.trans hDg)
      obtain ⟨z, hz, hzu⟩ := ih W q hqcov sq (compat_res F hWU (fun i : Fin n => f i.succ)
        (fun i => s i.succ) (fun i j => hcompat i.succ j.succ) q
        (fun i => res_basicOpen_le hWU (f i.succ)) rfl)
      let lhs := basisRestrictMap X.affineOpens F (mul_le_left (f 0) g) (s 0)
      let rhs := basisRestrictMap X.affineOpens F (mul_le_right (f 0) g) t
      have hl : ∀ i, basisRestrictMap X.affineOpens F
          (X.affineBasicOpen_le (V := W) (q i)) lhs = sq i := by
        intro i
        have hqP : (affineBasisOpen X (X.affineBasicOpen (q i))).obj ≤
            (affineBasisOpen X (X.affineBasicOpen (f 0 * f i.succ))).obj := by
          change X.basicOpen (q i) ≤ X.basicOpen (f 0 * f i.succ)
          rw [X.basicOpen_mul, X.basicOpen_res]
          exact le_inf (inf_le_left.trans (mul_le_left (f 0) g)) inf_le_right
        have := congrArg (basisRestrictMap X.affineOpens F hqP) (hcompat 0 i.succ)
        simpa only [lhs, sq, basisRestrictMap_comp] using this
      have hr : ∀ i, basisRestrictMap X.affineOpens F
          (X.affineBasicOpen_le (V := W) (q i)) rhs = sq i := by
        intro i
        have hqF : (affineBasisOpen X (X.affineBasicOpen (q i))).obj ≤
            (affineBasisOpen X (X.affineBasicOpen (f' i))).obj := by
          change X.basicOpen (q i) ≤ X.basicOpen (f' i)
          rw [X.basicOpen_res, X.basicOpen_res]
          exact le_inf (inf_le_left.trans hWV) inf_le_right
        have := congrArg (basisRestrictMap X.affineOpens F hqF) (ht i)
        simpa only [rhs, s', sq, basisRestrictMap_comp] using this
      obtain ⟨r, hr, hru⟩ := hpair U (f 0) g hpaircov (s 0) t
        (by simpa [lhs, rhs] using (hzu lhs hl).trans (hzu rhs hr).symm)
      refine ⟨r, ?_, ?_⟩
      · intro i
        cases i using Fin.cases with
        | zero => simpa using hr.1
        | succ i =>
          let Ui := X.affineBasicOpen (f i.succ)
          have hUiU : Ui.1 ≤ U.1 := X.affineBasicOpen_le (f i.succ)
          let a : Γ(X, Ui.1) :=
            X.presheaf.map (CategoryTheory.homOfLE hUiU).op (f 0)
          let b : Γ(X, Ui.1) :=
            X.presheaf.map (CategoryTheory.homOfLE hUiU).op g
          have hDa : X.basicOpen a = Ui.1 ⊓ X.basicOpen (f 0) :=
            X.basicOpen_res (f 0) (CategoryTheory.homOfLE hUiU).op
          have hDb : X.basicOpen b = Ui.1 ⊓ X.basicOpen g :=
            X.basicOpen_res g (CategoryTheory.homOfLE hUiU).op
          have hcovI : Ui.1 = X.basicOpen a ⊔ X.basicOpen b := by
            rw [hDa, hDb, ← inf_sup_left, ← hpaircov]
            exact (inf_eq_left.mpr hUiU).symm
          have hA0 : (affineBasisOpen X (X.affineBasicOpen a)).obj ≤
              (affineBasisOpen X (X.affineBasicOpen (f 0))).obj := res_basicOpen_le hUiU (f 0)
          have hVB : (affineBasisOpen X (X.affineBasicOpen b)).obj ≤
              (affineBasisOpen X V).obj := res_basicOpen_le hUiU g
          let sa := basisRestrictMap X.affineOpens F hA0 (s 0)
          let tb := basisRestrictMap X.affineOpens F hVB t
          let ri : F.obj (op (affineBasisOpen X Ui)) := basisRestrictMap X.affineOpens F hUiU r
          have hRiA : basisRestrictMap X.affineOpens F (X.affineBasicOpen_le (V := Ui) a) ri =
              sa := by
            have := congrArg (basisRestrictMap X.affineOpens F hA0) hr.1
            simpa only [ri, sa, basisRestrictMap_comp] using this
          have hRiB : basisRestrictMap X.affineOpens F (X.affineBasicOpen_le (V := Ui) b) ri =
              tb := by
            have := congrArg (basisRestrictMap X.affineOpens F hVB) hr.2
            simpa only [ri, tb, basisRestrictMap_comp] using this
          obtain ⟨u, hu, huuniq⟩ := hpair Ui a b hcovI sa tb (by
            rw [← hRiA, ← hRiB]
            simp [ri, basisRestrictMap_comp])
          have hSiA : basisRestrictMap X.affineOpens F (X.affineBasicOpen_le (V := Ui) a)
              (s i.succ) = sa := by
            have hP : (affineBasisOpen X (X.affineBasicOpen a)).obj ≤
                (affineBasisOpen X (X.affineBasicOpen (f i.succ * f 0))).obj := by
              change X.basicOpen a ≤ X.basicOpen (f i.succ * f 0)
              rw [hDa, X.basicOpen_mul]
              exact le_rfl
            have := congrArg (basisRestrictMap X.affineOpens F hP) (hcompat i.succ 0)
            simpa only [sa, basisRestrictMap_comp] using this
          have hSiB : basisRestrictMap X.affineOpens F (X.affineBasicOpen_le (V := Ui) b)
              (s i.succ) = tb := by
            have hWB : (affineBasisOpen X (X.affineBasicOpen b)).obj ≤
                (affineBasisOpen X (X.affineBasicOpen (f' i))).obj := by
              change X.basicOpen b ≤ X.basicOpen (f' i)
              rw [hDb, X.basicOpen_res]
              exact (inf_comm _ _).le
            have := congrArg (basisRestrictMap X.affineOpens F hWB) (ht i)
            simpa only [tb, s', basisRestrictMap_comp] using this.symm
          exact (huuniq ri ⟨hRiA, hRiB⟩).trans (huuniq (s i.succ) ⟨hSiA, hSiB⟩).symm
      · intro r' hr'
        let rV : F.obj (op (affineBasisOpen X V)) := basisRestrictMap X.affineOpens F hVU r'
        have hr'V : ∀ i, basisRestrictMap X.affineOpens F
            (X.affineBasicOpen_le (V := V) (f' i)) rV = s' i := by
          intro i
          have := congrArg (basisRestrictMap X.affineOpens F (res_basicOpen_le hVU (f i.succ)))
            (hr' i.succ)
          simpa only [rV, s', basisRestrictMap_comp] using this
        exact hru r' ⟨hr' 0, htu _ hr'V⟩

private lemma affine_fromSpec_reflect_le {X : Scheme.{u}} {U : X.Opens}
    (hU : IsAffineOpen U) {A B : X.Opens} (hA : A ≤ U)
    (hpre : hU.fromSpec ⁻¹ᵁ A ≤ hU.fromSpec ⁻¹ᵁ B) : A ≤ B := by
  intro x hx
  have hxU : x ∈ U := hA hx
  let p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hxU⟩
  have hfrom : hU.fromSpec p = x := by
    simpa [p] using hU.fromSpec_primeIdealOf ⟨x, hxU⟩
  have hpreA : p ∈ hU.fromSpec ⁻¹ᵁ A := by
    show hU.fromSpec p ∈ A
    simpa [hfrom] using hx
  have hpreB : p ∈ hU.fromSpec ⁻¹ᵁ B := hpre hpreA
  change hU.fromSpec p ∈ B at hpreB
  simpa [hfrom] using hpreB

/-- Every cover of an affine open `U` by opens `V i` is refined by finitely many standard opens
`D(f j)` of `U`, with `f j ∈ Γ(X, U)`, that cover `U`. -/
public lemma exists_finite_basicOpen_refinement_affine {X : Scheme.{u}}
    {U : X.Opens} (hU : IsAffineOpen U) {ι : Type*} (V : ι → X.Opens)
    (hcover : U ≤ ⨆ i, V i) :
    ∃ (n : ℕ) (f : Fin n → Γ(X, U)) (a : Fin n → ι),
      (⨆ j, X.basicOpen (f j)) = U ∧ ∀ j, X.basicOpen (f j) ≤ V (a j) := by
  classical
  let W : ι → TopologicalSpace.Opens (PrimeSpectrum Γ(X, U)) :=
    fun i => hU.fromSpec ⁻¹ᵁ V i
  have hcoverSpec : PrimeSpectrum.basicOpen (1 : Γ(X, U)) ≤ ⨆ i, W i := by
    intro p hp
    have hpU : p ∈ hU.fromSpec ⁻¹ᵁ U := by
      rw [hU.fromSpec_preimage_self]
      trivial
    have hx : hU.fromSpec p ∈ U := hpU
    obtain ⟨i, hi⟩ := Opens.mem_iSup.mp (hcover hx)
    exact Opens.mem_iSup.mpr ⟨i, hi⟩
  obtain ⟨n, f, a, hf, hfa⟩ :=
    PrimeSpectrum.exists_finite_basicOpen_refinement
      (f := (1 : Γ(X, U))) W hcoverSpec
  refine ⟨n, f, a, ?_, ?_⟩
  · apply le_antisymm
    · exact iSup_le fun j => X.basicOpen_le (f j)
    · intro x hx
      let p : PrimeSpectrum Γ(X, U) := hU.primeIdealOf ⟨x, hx⟩
      have hfrom : hU.fromSpec p = x := by
        simpa [p] using hU.fromSpec_primeIdealOf ⟨x, hx⟩
      have hp : p ∈ PrimeSpectrum.basicOpen (1 : Γ(X, U)) := by simp
      rw [hf] at hp
      obtain ⟨j, hj⟩ := Opens.mem_iSup.mp hp
      have hpre : p ∈ hU.fromSpec ⁻¹ᵁ X.basicOpen (f j) := by
        rwa [hU.fromSpec_preimage_basicOpen]
      change hU.fromSpec p ∈ X.basicOpen (f j) at hpre
      exact Opens.mem_iSup.mpr ⟨j, by simpa [hfrom] using hpre⟩
  · intro j
    apply affine_fromSpec_reflect_le hU (X.basicOpen_le (f j))
    rw [hU.fromSpec_preimage_basicOpen]
    exact hfa j

end Helpers

/-- A presheaf on the affine opens is (up to isomorphism) the restriction of a sheaf
if and only if it is a sheaf on the affine-open basis. -/
@[stacks 0F1A "equivalence of (1) and (2)", ega "0 3.2.2" "affine basis of a scheme"]
theorem isRestriction_iff_isSheafOnAffineBasis (X : Scheme.{u})
    (F : PresheafOnBasis X.affineOpens) :
    (∃ G : TopCat.Sheaf (Type u) (TopCat.of X),
      Nonempty (F ≅ restrictOfSheaf X.affineOpens G)) ↔
      IsSheafOnBasis X.affineOpens F := by
  constructor
  · rintro ⟨G, ⟨e⟩⟩
    exact isSheafOnBasis_of_iso e
      (Stacks.OpensBasis.isSheafOnBasis_restrict X.affineOpens X.isBasis_affineOpens G)
  · intro hF
    let R := Stacks.OpensBasis.restrictFunctor (X := TopCat.of X)
      (B := X.affineOpens) X.isBasis_affineOpens
    have : R.IsEquivalence := Stacks.OpensBasis.restrictFunctor_isEquivalence
      (X := TopCat.of X) (B := X.affineOpens) X.isBasis_affineOpens
    let F' : Stacks.OpensBasis.SheafOnBasis X.affineOpens := ⟨F, hF⟩
    let G : TopCat.Sheaf (Type u) (TopCat.of X) := R.objPreimage F'
    let e := R.objObjPreimageIso F'
    refine ⟨G, ?_⟩
    exact ⟨(Stacks.OpensBasis.isSheafOnBasisProp X.affineOpens).ι.mapIso e.symm⟩

/-- A presheaf on the affine-open basis is a sheaf exactly when its section set on the
empty open is a singleton and compatible sections glue uniquely across every standard
two-open cover of an affine open. -/
@[stacks 0F1A "equivalence of (2) and (3)"]
theorem isSheafOnAffineBasis_iff_standardPairs (X : Scheme.{u})
    (F : PresheafOnBasis X.affineOpens) :
    IsSheafOnBasis X.affineOpens F ↔
      ((∃! _s : F.obj (op (affineBasisOpen X ⟨⊥, isAffineOpen_bot X⟩)), True) ∧
      ∀ (U : X.affineOpens) (f g : Γ(X, U.1))
        (_hcov : U.1 = X.basicOpen f ⊔ X.basicOpen g)
        (s : F.obj (op (affineBasisOpen X (X.affineBasicOpen f))))
        (t : F.obj (op (affineBasisOpen X (X.affineBasicOpen g)))),
        (F.restrictMap X.affineOpens
            (show (affineBasisOpen X (X.affineBasicOpen (f * g))).obj ≤
                (affineBasisOpen X (X.affineBasicOpen f)).obj by
              change X.basicOpen (f * g) ≤ X.basicOpen f
              rw [X.basicOpen_mul]
              exact inf_le_left) s =
          F.restrictMap X.affineOpens
            (show (affineBasisOpen X (X.affineBasicOpen (f * g))).obj ≤
                (affineBasisOpen X (X.affineBasicOpen g)).obj by
              change X.basicOpen (f * g) ≤ X.basicOpen g
              rw [X.basicOpen_mul]
              exact inf_le_right) t) ↔
        ∃! r : F.obj (op (affineBasisOpen X U)),
          (F.restrictMap X.affineOpens (by exact (X.affineBasicOpen_le f)) r = s) ∧
          (F.restrictMap X.affineOpens (by exact (X.affineBasicOpen_le g)) r = t)) := by
  constructor
  · intro hF
    obtain ⟨hempty, hpairs⟩ := isSheafOnBasis_imp_emptyAndPairs X F hF
    refine ⟨hempty, ?_⟩
    intro U f g hcov s t
    constructor
    · exact hpairs U f g hcov s t
    · rintro ⟨r, ⟨hrs, hrt⟩, _⟩
      rw [← hrs, ← hrt, restrictMap_comp, restrictMap_comp]
  · rintro ⟨hempty, hpairs⟩
    have hpair : StandardPairProperty X F := by
      intro U f g hcov s t hagree
      exact (hpairs U f g hcov s t).mp hagree
    refine ⟨?_, ?_⟩
    · intro U ι 𝒰 hcov x y hagree
      let U' : X.affineOpens := ⟨U.obj, U.2⟩
      have hcover : U'.1 ≤ ⨆ i, (𝒰 i).obj := by
        show U.obj ≤ _
        rw [← hcov]
      obtain ⟨n, f, a, hfcov, hfsub⟩ :=
        exists_finite_basicOpen_refinement_affine U'.2 (fun i => (𝒰 i).obj) hcover
      let hsub : ∀ j : Fin n,
          (affineBasisOpen X (X.affineBasicOpen (f j))).obj ≤ (𝒰 (a j)).obj := fun j =>
        hfsub j
      let hCiU : ∀ j : ι, (𝒰 j).obj ≤ (affineBasisOpen X U').obj := fun j => by
        show (𝒰 j).obj ≤ U.obj
        rw [← hcov]
        exact le_iSup (fun k => (𝒰 k).obj) j
      let hfU : ∀ j : Fin n,
          (affineBasisOpen X (X.affineBasicOpen (f j))).obj ≤
            (affineBasisOpen X U').obj := fun j => (hsub j).trans (hCiU (a j))
      let t : ∀ j : Fin n,
          F.obj (op (affineBasisOpen X (X.affineBasicOpen (f j)))) := fun j =>
        F.restrictMap X.affineOpens (hfU j) x
      have htcompat := compat_single F f hfU x
      obtain ⟨r, hr, hrunique⟩ := finite_basicOpen_glue X F hempty hpair
        U' n f hfcov t htcompat
      have hx : ∀ j, F.restrictMap X.affineOpens
          (X.affineBasicOpen_le (V := U') (f j)) x = t j := fun _ => rfl
      have hy : ∀ j, F.restrictMap X.affineOpens
          (X.affineBasicOpen_le (V := U') (f j)) y = t j := by
        intro j
        have hlocal := congrArg
          (F.restrictMap X.affineOpens (hsub j)) (hagree (a j))
        simp only [restrictMap_comp] at hlocal
        exact hlocal.symm
      exact (hrunique x hx).trans (hrunique y hy).symm
    · intro U ι 𝒰 hcov s hcompat
      classical
      let U' : X.affineOpens := ⟨U.obj, U.2⟩
      have hcover : U'.1 ≤ ⨆ i, (𝒰 i).obj := by
        show U.obj ≤ _
        rw [← hcov]
      obtain ⟨n, f, a, hfcov, hfsub⟩ :=
        exists_finite_basicOpen_refinement_affine U'.2 (fun i => (𝒰 i).obj) hcover
      let t : ∀ j : Fin n,
          F.obj (op (affineBasisOpen X (X.affineBasicOpen (f j)))) := fun j =>
        F.restrictMap X.affineOpens
          (show (affineBasisOpen X (X.affineBasicOpen (f j))).obj ≤ (𝒰 (a j)).obj by
            exact hfsub j) (s (a j))
      have htcompat : ∀ i j : Fin n,
          F.restrictMap X.affineOpens (mul_le_left (f i) (f j)) (t i) =
            F.restrictMap X.affineOpens (mul_le_right (f i) (f j)) (t j) := by
        intro i j
        have h := hcompat (a i) (a j) (affineBasisOpen X (X.affineBasicOpen (f i * f j)))
          ((mul_le_left (f i) (f j)).trans (hfsub i)) ((mul_le_right (f i) (f j)).trans (hfsub j))
        dsimp [t]
        rw [restrictMap_comp, restrictMap_comp]
        exact h
      obtain ⟨r, hr⟩ := finite_basicOpen_glue X F hempty hpair
        U' n f hfcov t htcompat
      refine ⟨r, ?_⟩
      intro i
      let Ui : X.affineOpens := ⟨(𝒰 i).obj, (𝒰 i).2⟩
      have hUiU : (𝒰 i).obj ≤ U.obj := by
        rw [← hcov]
        exact le_iSup (fun j => (𝒰 j).obj) i
      let sUi := F.restrictMap X.affineOpens
        (show (affineBasisOpen X Ui).obj ≤ (affineBasisOpen X U').obj by exact hUiU) r
      let g : Fin n → Γ(X, Ui.1) := fun j =>
        X.presheaf.map (CategoryTheory.homOfLE hUiU).op (f j)
      have hgcov := iSup_basicOpen_res (V := Ui.1) hUiU f (hUiU.trans hfcov.ge)
      let q : ∀ j : Fin n,
          F.obj (op (affineBasisOpen X (X.affineBasicOpen (g j)))) := fun j =>
        F.restrictMap X.affineOpens
          (X.affineBasicOpen_le (V := Ui) (g j)) (s i)
      have hqcompat := compat_single F g (fun j => X.affineBasicOpen_le (V := Ui) (g j)) (s i)
      obtain ⟨_, _, hqunique⟩ := finite_basicOpen_glue X F hempty hpair
        Ui n g hgcov q hqcompat
      have hsUi : ∀ j,
          F.restrictMap X.affineOpens
            (X.affineBasicOpen_le (V := Ui) (g j)) sUi = q j := by
        intro j
        have hVf := res_basicOpen_le (V := Ui) hUiU (f j)
        have h1 := congrArg (F.restrictMap X.affineOpens hVf) (hr.1 j)
        have e : ∀ {A B : BasisCat X.affineOpens} (h : B.obj ≤ A.obj) (x : F.obj (op A)),
            F.restrictMap X.affineOpens h x = basisRestrictMap X.affineOpens F h x := fun _ _ => rfl
        simp only [sUi, t, q, e, basisRestrictMap_comp] at h1 ⊢
        exact h1.trans (hcompat i (a j) (affineBasisOpen X (X.affineBasicOpen (g j)))
          (X.affineBasicOpen_le (V := Ui) (g j)) (hVf.trans (hfsub j))).symm
      show sUi = s i
      exact (hqunique sUi hsUi).trans (hqunique (s i) (fun _ => rfl)).symm

end AlgebraicGeometry.Scheme

end
