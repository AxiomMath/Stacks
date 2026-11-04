module

public import StacksFrontier.AlgebraicGeometry.Different.DedekindDifferent.RingEquivTransport
public import Mathlib.AlgebraicGeometry.Scheme

/-!
# The Dedekind setup on the global sections of `Spec B → Spec A`

The hypotheses of the Dedekind different of `A → B` transfer to the map of global sections
`Γ(Spec A, ⊤) → Γ(Spec B, ⊤)` along the canonical isomorphisms `A ≅ Γ(Spec A, ⊤)` and
`B ≅ Γ(Spec B, ⊤)`; `1` lies in one complementary module exactly when it lies in the other, and
the Dedekind different ideal on `Spec` is the image of the one of `B`.
-/

@[expose] public noncomputable section

open scoped TensorProduct
open AlgebraicGeometry CategoryTheory

universe u

namespace Stacks.Discriminant

variable {A B : Type u} [CommRing A] [CommRing B] [Algebra A B]

/-- The Dedekind setup of `A → B` transported to the global sections of
`Spec B → Spec A`. -/
@[instance_reducible]
def DedekindDifferentSetup.toSpec (setup : DedekindDifferentSetup A B) :
    letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
      (Spec.map (CommRingCat.ofHom (algebraMap A B))).appTop.hom.toAlgebra
    DedekindDifferentSetup Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
  letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
    (Spec.map (CommRingCat.ofHom (algebraMap A B))).appTop.hom.toAlgebra
  setup.ofRingEquiv (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
    (Scheme.ΓSpecIso (CommRingCat.of B)).symm.commRingCatIsoToRingEquiv
    fun a => (congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B)))).symm

/-- One lies in the complementary module of the setup on `Spec` exactly when it lies in the
complementary module of `A → B`. -/
theorem DedekindDifferentSetup.one_mem_complementaryModule_toSpec_iff
    (setup : DedekindDifferentSetup A B) :
    letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
      (Spec.map (CommRingCat.ofHom (algebraMap A B))).appTop.hom.toAlgebra
    (1 : Γ(Spec (CommRingCat.of B), ⊤) ⊗[Γ(Spec (CommRingCat.of A), ⊤)]
        FractionRing Γ(Spec (CommRingCat.of A), ⊤)) ∈ setup.toSpec.complementaryModule ↔
      (1 : B ⊗[A] FractionRing A) ∈ setup.complementaryModule :=
  let : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
    (Spec.map (CommRingCat.ofHom (algebraMap A B))).appTop.hom.toAlgebra
  setup.one_mem_complementaryModule_ofRingEquiv_iff
    (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
    (Scheme.ΓSpecIso (CommRingCat.of B)).symm.commRingCatIsoToRingEquiv
    fun a => (congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B)))).symm

/-- The Dedekind different ideal of the setup on `Spec` is the image of the one of `A → B`
under `B ≅ Γ(Spec B, ⊤)`. -/
theorem DedekindDifferentSetup.dedekindDifferentIdeal_toSpec
    (setup : DedekindDifferentSetup A B) :
    letI : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
      (Spec.map (CommRingCat.ofHom (algebraMap A B))).appTop.hom.toAlgebra
    dedekindDifferentIdeal setup.toSpec =
      (dedekindDifferentIdeal setup).map (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom :=
  let : Algebra Γ(Spec (CommRingCat.of A), ⊤) Γ(Spec (CommRingCat.of B), ⊤) :=
    (Spec.map (CommRingCat.ofHom (algebraMap A B))).appTop.hom.toAlgebra
  setup.dedekindDifferentIdeal_ofRingEquiv
    (Scheme.ΓSpecIso (CommRingCat.of A)).symm.commRingCatIsoToRingEquiv
    (Scheme.ΓSpecIso (CommRingCat.of B)).symm.commRingCatIsoToRingEquiv
    fun a => (congrArg (fun φ => φ.hom a)
      (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B)))).symm

end Stacks.Discriminant

end
