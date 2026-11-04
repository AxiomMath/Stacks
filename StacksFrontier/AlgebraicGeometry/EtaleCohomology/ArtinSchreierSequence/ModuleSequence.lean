module

public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.ArtinSchreierSequence.ConstantKernel
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.EtaleModulesConstantRing
public import StacksFrontier.AlgebraicGeometry.EtaleCohomology.LAdicSheaves.UnderlyingTower
public import StacksFrontier.Algebra.Category.ModuleCat.Sheaf.ConstantSheafForgetAbelian

/-!
# The Artin–Schreier sequence as a sequence of sheaves of `𝔽_p`-modules

Let `p` be a prime and `X` a scheme on which `p` vanishes. The sheaf `𝐆_a` of global functions on
the small étale site of `X` is annihilated by `p`, hence is a sheaf of `𝔽_p`-modules, and every
morphism of abelian sheaves between sheaves annihilated by `p` is `𝔽_p`-linear. So the
Artin–Schreier sequence `0 ⟶ 𝐙/p𝐙 ⟶ 𝐆_a ⟶ 𝐆_a ⟶ 0` of [Stacks, Tag 0A3J] is a short exact
sequence in `Stacks.EtaleCohomology.EtaleModules (ZMod p) X`, the first term being the constant
sheaf of `𝔽_p`-modules with value `𝔽_p`.

## Main definitions

* `Stacks.ArtinSchreier.zmodAdditiveSheaf`: `𝐆_a` as a sheaf of `𝔽_p`-modules.
* `Stacks.ArtinSchreier.zmodFrobenius`: the Frobenius `x ↦ x ^ p` of it.
* `Stacks.ArtinSchreier.zmodConstantHom`: the inclusion of the constant sheaf `𝔽_p`.
* `Stacks.ArtinSchreier.zmodArtinSchreierSequence`: the sequence
  `𝔽_p ⟶ 𝐆_a ⟶ 𝐆_a`, the second map being `x ↦ x ^ p - x`.

## Main results

* `Stacks.ArtinSchreier.zmodArtinSchreierSequence_shortExact`: it is short exact.
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite AlgebraicGeometry Stacks.EtaleCohomology

universe u

namespace Stacks.ArtinSchreier

variable (X : Scheme.{u}) {p : ℕ} (hp : p.Prime) (hX : (p : Γ(X, ⊤)) = 0)

include hX in
/-- The sections of `𝐆_a` are annihilated by `p` when `p` vanishes on `X`. -/
theorem nsmul_additiveSheaf_eq_zero (U : X.Etaleᵒᵖ)
    (x : ToType ((additiveSheaf.{u, 0} X).obj.obj U)) : p • x = 0 := by
  obtain ⟨y⟩ := x
  let z : Γ(U.unop.left, ⊤) := y
  have h : (p : Γ(U.unop.left, ⊤)) * z = 0 := by
    rw [natCast_eq_zero_of_etale X hX U.unop, zero_mul]
  exact congrArg ULift.up ((nsmul_eq_mul p z).trans h)

/-- **`𝐆_a` as a sheaf of `𝔽_p`-modules** on the small étale site of a scheme on which `p`
vanishes. -/
def zmodAdditiveSheaf : EtaleModules.{u, 0} (ZMod p) X :=
  zmodSheafOfAnnihilated.{u + 1, 0, u} X.smallEtaleTopology p (additiveSheaf.{u, 0} X)
    (nsmul_additiveSheaf_eq_zero X hX)

/-- Forgetting the `𝔽_p`-module structure of `Stacks.ArtinSchreier.zmodAdditiveSheaf` gives
`𝐆_a`. -/
def zmodAdditiveSheafForgetIso :
    (etaleModuleForgetAb.{u, 0} (ZMod p) X).obj (zmodAdditiveSheaf X hX) ≅
      additiveSheaf.{u, 0} X :=
  zmodSheafOfAnnihilatedIso.{u + 1, 0, u} X.smallEtaleTopology p (additiveSheaf.{u, 0} X)
    (nsmul_additiveSheaf_eq_zero X hX)

/-- Forgetting the `𝔽_p`-module structure of étale sheaves of `𝔽_p`-modules is fully faithful:
an additive map between groups annihilated by `p` is `𝔽_p`-linear. -/
def etaleModuleForgetZModFullyFaithful (p : ℕ) :
    (etaleModuleForgetAb.{u, 0} (ZMod p) X).FullyFaithful :=
  haveI := forget₂_zmod_full.{u + 1} p
  Functor.FullyFaithful.ofFullyFaithful _

/-- Forgetting the `𝔽_p`-module structure of étale sheaves of `𝔽_p`-modules is full. -/
instance (p : ℕ) : (etaleModuleForgetAb.{u, 0} (ZMod p) X).Full :=
  (etaleModuleForgetZModFullyFaithful X p).full

/-- Forgetting the `𝔽_p`-module structure of étale sheaves of `𝔽_p`-modules is faithful. -/
instance (p : ℕ) : (etaleModuleForgetAb.{u, 0} (ZMod p) X).Faithful :=
  (etaleModuleForgetZModFullyFaithful X p).faithful

/-- **The Frobenius `x ↦ x ^ p` of `𝐆_a`**, as an endomorphism of sheaves of `𝔽_p`-modules. -/
def zmodFrobenius : zmodAdditiveSheaf X hX ⟶ zmodAdditiveSheaf X hX :=
  (etaleModuleForgetZModFullyFaithful X p).preimage
    ((zmodAdditiveSheafForgetIso X hX).hom ≫ frobeniusMap.{u, 0} X hp hX ≫
      (zmodAdditiveSheafForgetIso X hX).inv)

/-- The underlying morphism of abelian sheaves of `zmodFrobenius` is `frobeniusMap`, transported
along `zmodAdditiveSheafForgetIso`. -/
theorem etaleModuleForget_map_zmodFrobenius :
    (etaleModuleForgetAb.{u, 0} (ZMod p) X).map (zmodFrobenius X hp hX) =
      (zmodAdditiveSheafForgetIso X hX).hom ≫ frobeniusMap.{u, 0} X hp hX ≫
        (zmodAdditiveSheafForgetIso X hX).inv :=
  (etaleModuleForgetZModFullyFaithful X p).map_preimage _

/-- The constant sheaf of `𝔽_p`-modules with value `𝔽_p`, in the coefficient universe of
`Stacks.EtaleCohomology.EtaleModules`. -/
abbrev zmodConstantSheaf (p : ℕ) : EtaleModules.{u, 0} (ZMod p) X :=
  (constantSheaf X.smallEtaleTopology (ModuleCat.{u + 1} (ZMod p))).obj
    (ModuleCat.of (ZMod p) (ULift.{u + 1} (ZMod p)))

/-- Forgetting the module structure of the constant sheaf `𝔽_p` gives the constant abelian sheaf
`𝐙/p𝐙`. -/
def zmodConstantSheafForgetIso (p : ℕ) :
    (etaleModuleForgetAb.{u, 0} (ZMod p) X).obj (zmodConstantSheaf X p) ≅
      (constantSheaf X.smallEtaleTopology AddCommGrpCat.{u + 1}).obj
        (AddCommGrpCat.of (ULift.{u + 1} (ZMod p))) :=
  (Stacks.ModuleCatLift.constantSheafForget₂Iso.{u + 1} (ZMod p) X.smallEtaleTopology).app
    (ModuleCat.of (ZMod p) (ULift.{u + 1} (ZMod p)))

/-- **The inclusion of the constant sheaf `𝔽_p` into `𝐆_a`**, as a morphism of sheaves of
`𝔽_p`-modules: the residue classes go to the scalar functions. -/
def zmodConstantHom : zmodConstantSheaf X p ⟶ zmodAdditiveSheaf X hX :=
  (etaleModuleForgetZModFullyFaithful X p).preimage
    ((zmodConstantSheafForgetIso X p).hom ≫ zmodSheafHom.{u, 0} X hX ≫
      (zmodAdditiveSheafForgetIso X hX).inv)

/-- The underlying morphism of abelian sheaves of `zmodConstantHom` is `zmodSheafHom`, transported
along `zmodConstantSheafForgetIso` and `zmodAdditiveSheafForgetIso`. -/
theorem etaleModuleForget_map_zmodConstantHom :
    (etaleModuleForgetAb.{u, 0} (ZMod p) X).map (zmodConstantHom X hX) =
      (zmodConstantSheafForgetIso X p).hom ≫ zmodSheafHom.{u, 0} X hX ≫
        (zmodAdditiveSheafForgetIso X hX).inv :=
  (etaleModuleForgetZModFullyFaithful X p).map_preimage _

/-- **The Artin–Schreier map `x ↦ x ^ p - x`** on `𝐆_a`, as a morphism of sheaves of
`𝔽_p`-modules. -/
abbrev zmodArtinSchreierMap : zmodAdditiveSheaf X hX ⟶ zmodAdditiveSheaf X hX :=
  zmodFrobenius X hp hX - 𝟙 _

/-- The underlying morphism of abelian sheaves of `zmodArtinSchreierMap` is `artinSchreierMap`,
transported along `zmodAdditiveSheafForgetIso`. -/
theorem etaleModuleForget_map_zmodArtinSchreierMap :
    (etaleModuleForgetAb.{u, 0} (ZMod p) X).map (zmodArtinSchreierMap X hp hX) =
      (zmodAdditiveSheafForgetIso X hX).hom ≫ artinSchreierMap.{u, 0} X hp hX ≫
        (zmodAdditiveSheafForgetIso X hX).inv := by
  rw [Functor.map_sub, CategoryTheory.Functor.map_id, etaleModuleForget_map_zmodFrobenius,
    artinSchreierMap, Preadditive.sub_comp, Preadditive.comp_sub, Category.id_comp,
    Iso.hom_inv_id]

/-- The inclusion of `𝔽_p` into `𝐆_a` followed by the Artin–Schreier map is zero. -/
theorem zmodConstantHom_comp_zmodArtinSchreierMap :
    zmodConstantHom X hX ≫ zmodArtinSchreierMap X hp hX = 0 :=
  (etaleModuleForgetAb.{u, 0} (ZMod p) X).map_injective (by
    rw [Functor.map_comp, Functor.map_zero, etaleModuleForget_map_zmodConstantHom,
      etaleModuleForget_map_zmodArtinSchreierMap]
    simp only [Category.assoc, Iso.inv_hom_id_assoc]
    rw [reassoc_of% (zmodSheafHom_comp_artinSchreierMap X hp hX), zero_comp, comp_zero])

/-- **The Artin–Schreier sequence** `𝔽_p ⟶ 𝐆_a ⟶ 𝐆_a` of sheaves of `𝔽_p`-modules on the small
étale site of a scheme on which `p` vanishes. -/
def zmodArtinSchreierSequence : ShortComplex (EtaleModules.{u, 0} (ZMod p) X) :=
  ShortComplex.mk (zmodConstantHom X hX) (zmodArtinSchreierMap X hp hX)
    (zmodConstantHom_comp_zmodArtinSchreierMap X hp hX)

/-- Forgetting the module structure carries the Artin–Schreier sequence of sheaves of
`𝔽_p`-modules to the Artin–Schreier sequence of abelian sheaves. -/
def zmodArtinSchreierSequenceMapIso :
    (zmodArtinSchreierSequence X hp hX).map (etaleModuleForgetAb.{u, 0} (ZMod p) X) ≅
      constantArtinSchreierSequence.{u, 0} X hp hX :=
  ShortComplex.isoMk (zmodConstantSheafForgetIso X p) (zmodAdditiveSheafForgetIso X hX)
    (zmodAdditiveSheafForgetIso X hX)
    (by
      change (zmodConstantSheafForgetIso X p).hom ≫ zmodSheafHom.{u, 0} X hX =
        (etaleModuleForgetAb.{u, 0} (ZMod p) X).map (zmodConstantHom X hX) ≫
          (zmodAdditiveSheafForgetIso X hX).hom
      rw [etaleModuleForget_map_zmodConstantHom]
      simp)
    (by
      change (zmodAdditiveSheafForgetIso X hX).hom ≫ artinSchreierMap.{u, 0} X hp hX =
        (etaleModuleForgetAb.{u, 0} (ZMod p) X).map (zmodArtinSchreierMap X hp hX) ≫
          (zmodAdditiveSheafForgetIso X hX).hom
      rw [etaleModuleForget_map_zmodArtinSchreierMap]
      simp)

/-- **[Stacks, Tag 0A3J] for sheaves of `𝔽_p`-modules.** On a scheme on which the prime `p`
vanishes, `0 ⟶ 𝔽_p ⟶ 𝐆_a ⟶ 𝐆_a ⟶ 0` is a short exact sequence of sheaves of `𝔽_p`-modules on the
small étale site, the second map being `x ↦ x ^ p - x`. -/
theorem zmodArtinSchreierSequence_shortExact :
    (zmodArtinSchreierSequence X hp hX).ShortExact := by
  have h := ShortComplex.shortExact_of_iso (zmodArtinSchreierSequenceMapIso X hp hX).symm
    (constantArtinSchreierSequence_shortExact.{u, 0} X hp hX)
  exact ShortComplex.ShortExact.mk'
    ((ShortComplex.exact_map_iff_of_faithful _ (etaleModuleForgetAb.{u, 0} (ZMod p) X)).1 h.exact)
    ((etaleModuleForgetAb.{u, 0} (ZMod p) X).mono_of_mono_map h.mono_f)
    ((etaleModuleForgetAb.{u, 0} (ZMod p) X).epi_of_epi_map h.epi_g)

end Stacks.ArtinSchreier

end
