module

public import StacksFrontier.AlgebraicGeometry.Duality.TwistedInverseImageFTS.Independence

/-!
# The upper shriek functor and composition

The upper shriek functor of [Stacks, Tag 0A9Y] turns composition into composition. Two pieces are
here: the case of an open immersion followed by a morphism, which holds outright, and the general
case, constructed through a compactification of the composite proper over a compactification of
the second factor, conditional on the maps of [Stacks, Tag 0A9L] being invertible.

Let `S` be a quasi-compact quasi-separated scheme and let `f : X ⟶ Y` be a morphism of
`AlgebraicGeometry.FTS S` with a compactification `c`. Precomposing with an open immersion
`j : U ⟶ X` gives a compactification `c.precompOpen j` of `j ≫ f`: the open immersion
`U ⟶ X ⟶ X̄` followed by the same proper morphism `X̄ ⟶ Y`. At that compactification the
upper shriek functor of [Stacks, Tag 0A9Y] satisfies `(j ≫ f)^! ≅ Lj^* ∘ f^!`, the derived
pullbacks along `U ⟶ X ⟶ X̄` composing.

## Main definitions

* `AlgebraicGeometry.CompactificationOf.precompOpen` — the compactification of `j ≫ f` obtained
  from one of `f` and an open immersion `j`.
* `Stacks.Duality.quasiCoherentDerivedPullbackCompIso` — `L(f₁ ≫ f₂)^* ≅ Lf₁^* ∘ Lf₂^*` on the
  quasi-coherent derived categories.
* `Stacks.Duality.upperShriekPrecompOpenIso` — `(j ≫ f)^! ≅ Lj^* ∘ f^!` at the compactification
  `c.precompOpen j`.
* `Stacks.Duality.CompCompactification.compactification` and `restrictCompactification` — for
  `f : X ⟶ Y`, `g : Y ⟶ Z` and compactifications `Y ⊆ Ȳ` of `g` and `X ⊆ X̄` of `f ≫ g`, the
  closure `P` of the graph of `X ⟶ Y ⟶ Ȳ` in `X̄ ×_Z Ȳ` is a compactification of `X` over `Z`
  proper over `Ȳ`, and its inverse image `Q = P ×_Ȳ Y` is a compactification of `X` over `Y`.
* `Stacks.Duality.CompCompactification.upperShriekObjIso` — `(f ≫ g)^! K ≅ f^!(g^! K)` computed at
  `P` and `Q`, wherever the map of [Stacks, Tag 0A9L] for `Q ⊆ P` is invertible.
* `Stacks.Duality.CompCompactification.upperShriekCompObjIsoOfIsIso` — the same at arbitrary
  compactifications, wherever the maps of [Stacks, Tag 0A9L] involved are invertible; this is
  the content of [Stacks, Tag 0ATX] and [Stacks, Tag 0AA0] once [Stacks, Tag 0A9P] supplies the
  invertibility on `D⁺_QCoh`.

## References

* [Stacks Project, Tag 0A9Y](https://stacks.math.columbia.edu/tag/0A9Y)
* [Stacks Project, Tag 0G4J](https://stacks.math.columbia.edu/tag/0G4J)
* [Stacks Project, Tag 0ATX](https://stacks.math.columbia.edu/tag/0ATX)
* [Stacks Project, Tag 0AA0](https://stacks.math.columbia.edu/tag/0AA0)
* [Stacks Project, Tag 0A9L](https://stacks.math.columbia.edu/tag/0A9L)
* [Stacks Project, Tag 0A9P](https://stacks.math.columbia.edu/tag/0A9P)
-/

-- This file uses the locally small derived-category models below, which are not
-- global instances (see `StacksFrontier.Homology.DerivedCategory.LocallySmall`):
-- `D(𝒪_X)` for a scheme.
attribute [local instance] AlgebraicGeometry.Scheme.Modules.hasDerivedCategory

@[expose] public noncomputable section

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits

universe u

namespace AlgebraicGeometry.CompactificationOf

variable {T : Scheme.{u}} {X : Over T}

/-- A compactification `X ⟶ X̄` of `X` over `T` restricts along an open immersion `i : U ⟶ X`
to a compactification of `U` over `T`: `U ⟶ X ⟶ X̄` is an open immersion and `X̄` is still
proper over `T`. -/
def precompOpen (c : CompactificationOf X) {U : Scheme.{u}} (i : U ⟶ X.left)
    [IsOpenImmersion i] : CompactificationOf (Over.mk (i ≫ X.hom)) :=
  ⟨StructuredArrow.mk (Y := c.obj.right)
      (Over.homMk (i ≫ c.immersion) (by
        simp only [Over.mk_left, Over.mk_hom, Functor.id_obj, Category.assoc]
        congr 1
        exact Over.w c.obj.hom)),
    ⟨(inferInstance : IsOpenImmersion (i ≫ c.immersion)), (inferInstance : IsProper c.toBase)⟩⟩

variable (c : CompactificationOf X) {U : Scheme.{u}} (i : U ⟶ X.left) [IsOpenImmersion i]

/-- The space of `c.precompOpen i` is the space `X̄` of `c`. -/
@[simp]
theorem precompOpen_space : (c.precompOpen i).space = c.space :=
  rfl

/-- The open immersion of `c.precompOpen i` is the composite `U ⟶ X ⟶ X̄`. -/
@[simp]
theorem precompOpen_immersion : (c.precompOpen i).immersion = i ≫ c.immersion :=
  rfl

/-- The proper morphism `X̄ ⟶ T` of `c.precompOpen i` is that of `c`. -/
@[simp]
theorem precompOpen_toBase : (c.precompOpen i).toBase = c.toBase :=
  rfl

end AlgebraicGeometry.CompactificationOf

namespace Stacks.Duality

/-- **Derived pullback of a composite on the quasi-coherent derived categories**:
`Lf₂^* ⋙ Lf₁^* ≅ L(f₁ ≫ f₂)^*`, the ambient composition formula
`Stacks.Duality.derivedPullbackCompIso` read on the full subcategories. -/
def quasiCoherentDerivedPullbackCompIso {X Y Z : Scheme.{u}} (f₁ : X ⟶ Y) (f₂ : Y ⟶ Z) :
    quasiCoherentDerivedPullback' f₂ ⋙ quasiCoherentDerivedPullback' f₁ ≅
      quasiCoherentDerivedPullback' (f₁ ≫ f₂) :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _ ((derivedPullbackCompIso f₁ f₂).app K.obj))
    (fun e => ObjectProperty.hom_ext _ ((derivedPullbackCompIso f₁ f₂).hom.naturality e.hom))

/-- Derived pullback on `D_QCoh` along equal morphisms: the two functors are isomorphic, the
ambient components being the identity. -/
def quasiCoherentDerivedPullbackCongr {X Y : Scheme.{u}} {h₁ h₂ : X ⟶ Y} (e : h₁ = h₂) :
    quasiCoherentDerivedPullback' h₁ ≅ quasiCoherentDerivedPullback' h₂ :=
  NatIso.ofComponents
    (fun K => ObjectProperty.isoMk _
      (eqToIso (congrArg (fun h : X ⟶ Y => (derivedPullback h).obj K.obj) e)))
    (fun _ => by
      subst e
      exact ObjectProperty.hom_ext _ ((Category.comp_id _).trans (Category.id_comp _).symm))

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {U X Y : FTS S}
  (j : U ⟶ X) [IsOpenImmersion j.left] (f : X ⟶ Y)
  (c : CompactificationOf (Over.mk f.left))

/-- **The upper shriek of `j ≫ f` for an open immersion `j`, at the restricted
compactification.** For `j : U ⟶ X` a morphism of `FTS S` whose underlying morphism is an open
immersion and `c` a compactification of `f : X ⟶ Y`, computing `(j ≫ f)^!` at
`c.precompOpen j.left` gives `Lj^* ∘ f^!`: both are `L(U ⟶ X̄)^* ∘ ā` for the twisted inverse
image `ā` of `X̄ ⟶ Y`. -/
def upperShriekPrecompOpenIso :
    upperShriek (j ≫ f) (c.precompOpen j.left) ≅
      upperShriek f c ⋙ quasiCoherentDerivedPullback' j.left :=
  Functor.isoWhiskerLeft
      (twistedInverseImage c.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs c.toBase))
      (quasiCoherentDerivedPullbackCompIso j.left c.immersion).symm ≪≫
    (Functor.associator _ _ _).symm

end Stacks.Duality

namespace Stacks.Duality

/-- **The two left adjoints of `Rj_*` on `D_QCoh` agree**: restriction `j^*` and derived pullback
`Lj^*` along an open immersion `j` of quasi-compact and quasi-separated schemes are both left
adjoint to `Rj_*`, hence canonically isomorphic. -/
def restrictedDerivedRestrictAdjointIso {U Z : Scheme.{u}} (i : U ⟶ Z) [IsOpenImmersion i]
    [CompactSpace U] [QuasiSeparatedSpace U] [CompactSpace Z] [QuasiSeparatedSpace Z] :
    OpenImmersion.restrictedDerivedRestrict i ≅ quasiCoherentDerivedPullback' i :=
  (OpenImmersion.quasiCoherentDerivedRestrictAdjunction i
      (OpenImmersion.isQuasicoherent_homology_derivedRestrict i)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs i)).leftAdjointUniq
    (quasiCoherentDerivedAdjunction i (isQuasicoherent_homology_derivedPullback' i)
      (isQuasicoherent_homology_derivedPushforward_of_qcqs i))

end Stacks.Duality

namespace Stacks.Duality.CompCompactification

variable {S : Scheme.{u}} [CompactSpace S] [QuasiSeparatedSpace S] {X Y Z : FTS S}
  (f : X ⟶ Y) (g : Y ⟶ Z) (cg : CompactificationOf (Over.mk g.left))
  (cfg : CompactificationOf (Over.mk (f ≫ g).left))

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- The two factorisations of `X ⟶ Z` through the compactifications agree. -/
theorem comm : cfg.immersion ≫ cfg.toBase = f.left ≫ cg.immersion ≫ cg.toBase := by
  rw [immersion_comp_toBase (f ≫ g) cfg, immersion_comp_toBase g cg]
  rfl

/-- The graph `X ⟶ X̄ ×_Z Ȳ` of `X ⟶ Y ⟶ Ȳ`, paired with the open immersion `X ⟶ X̄`. -/
abbrev graph : X.left ⟶ pullback cfg.toBase cg.toBase :=
  GraphClosure.graph cfg.toBase cg.toBase cfg.immersion cg.immersion f.left (comm f g cg cfg)

/-- `X̄ ×_Z Ȳ` is quasi-separated, being separated over `X̄`. -/
instance quasiSeparatedSpace_pullback :
    QuasiSeparatedSpace (pullback cfg.toBase cg.toBase : Scheme.{u}) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.fst cfg.toBase cg.toBase)

/-- The graph is quasi-compact: `X` is quasi-compact and `X̄ ×_Z Ȳ` quasi-separated. -/
instance quasiCompact_graph : QuasiCompact (graph f g cg cfg) :=
  @quasiCompact_of_compactSpace _ _ _ (inferInstanceAs (CompactSpace X.left)) _

/-- The scheme-theoretic closure `P` of the graph. -/
abbrev space : Scheme.{u} := (graph f g cg cfg).image

/-- The open immersion `X ⟶ P`. -/
abbrev ι : X.left ⟶ space f g cg cfg := (graph f g cg cfg).toImage

/-- The projection `P ⟶ Ȳ`. -/
abbrev proj : space f g cg cfg ⟶ cg.space :=
  GraphClosure.closureSnd cfg.toBase cg.toBase cfg.immersion cg.immersion f.left (comm f g cg cfg)

omit [CompactSpace S] [QuasiSeparatedSpace S] in
/-- `X ⟶ P ⟶ Ȳ` is `X ⟶ Y ⟶ Ȳ`. -/
theorem ι_proj : ι f g cg cfg ≫ proj f g cg cfg = f.left ≫ cg.immersion :=
  GraphClosure.toImage_closureSnd _ _ _ _ _ _

/-- `P` is quasi-compact, being proper over the quasi-compact `Ȳ`. -/
instance compactSpace_space : CompactSpace (space f g cg cfg) :=
  QuasiCompact.compactSpace_of_compactSpace (proj f g cg cfg)

/-- `P` is quasi-separated, being separated over the quasi-separated `Ȳ`. -/
instance quasiSeparatedSpace_space : QuasiSeparatedSpace (space f g cg cfg) :=
  quasiSeparatedSpace_of_quasiSeparated (proj f g cg cfg)

/-- `P` as a compactification of `X` over `Z`: `X ⟶ P` is an open immersion and `P ⟶ Ȳ ⟶ Z` is
proper. -/
def compactification : CompactificationOf (Over.mk (f ≫ g).left) :=
  ⟨StructuredArrow.mk (Y := Over.mk (proj f g cg cfg ≫ cg.toBase))
      (Over.homMk (ι f g cg cfg) (by
        simp only [Over.mk_left, Over.mk_hom, Functor.id_obj]
        rw [← Category.assoc, ι_proj, Category.assoc, immersion_comp_toBase g cg]
        rfl)),
    ⟨(inferInstance : IsOpenImmersion (ι f g cg cfg)),
      (inferInstance : IsProper (proj f g cg cfg ≫ cg.toBase))⟩⟩

/-- The inverse image `Q = P ×_Ȳ Y` of `Y` in `P`. -/
abbrev restrictSpace : Scheme.{u} := pullback (proj f g cg cfg) cg.immersion

/-- The open immersion `X ⟶ Q`. -/
abbrev restrictι : X.left ⟶ restrictSpace f g cg cfg :=
  pullback.lift (ι f g cg cfg) f.left (ι_proj f g cg cfg)

/-- `X ⟶ Q` is an open immersion: followed by the open immersion `Q ⟶ P` it is `X ⟶ P`. -/
instance isOpenImmersion_restrictι : IsOpenImmersion (restrictι f g cg cfg) := by
  have : IsOpenImmersion (restrictι f g cg cfg ≫ pullback.fst _ _) := by
    rw [pullback.lift_fst]
    infer_instance
  exact IsOpenImmersion.of_comp _ (pullback.fst (proj f g cg cfg) cg.immersion)

/-- `Q` is quasi-compact, being proper over `Y`. -/
instance compactSpace_restrictSpace : CompactSpace (restrictSpace f g cg cfg) :=
  QuasiCompact.compactSpace_of_compactSpace (pullback.snd (proj f g cg cfg) cg.immersion)

/-- `Q` is quasi-separated, being separated over `Y`. -/
instance quasiSeparatedSpace_restrictSpace : QuasiSeparatedSpace (restrictSpace f g cg cfg) :=
  quasiSeparatedSpace_of_quasiSeparated (pullback.snd (proj f g cg cfg) cg.immersion)

/-- `Q` as a compactification of `X` over `Y`: `X ⟶ Q` is an open immersion and `Q ⟶ Y`, the
base change of the proper `P ⟶ Ȳ`, is proper. -/
def restrictCompactification : CompactificationOf (Over.mk f.left) :=
  ⟨StructuredArrow.mk (Y := Over.mk (pullback.snd (proj f g cg cfg) cg.immersion))
      (Over.homMk (restrictι f g cg cfg) (pullback.lift_snd _ _ _)),
    ⟨(inferInstance : IsOpenImmersion (restrictι f g cg cfg)),
      (inferInstance : IsProper (pullback.snd (proj f g cg cfg) cg.immersion))⟩⟩

/-- The map of [Stacks, Tag 0A9L] for the cartesian square `Q ⟶ P`, `Q ⟶ Y` over `P ⟶ Ȳ ⟵ Y`. -/
abbrev restrictionMap :=
  OpenImmersion.twistedInverseImageRestrictionMap (pullback.fst (proj f g cg cfg) cg.immersion)
    (pullback.snd (proj f g cg cfg) cg.immersion) (proj f g cg cfg) cg.immersion
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (isQuasicoherent_homology_derivedPushforward_of_qcqs _)
    (OpenImmersion.isQuasicoherent_homology_derivedRestrict _)
    (OpenImmersion.isQuasicoherent_homology_derivedRestrict _)
    (IsPullback.of_hasPullback _ _)

/-- `a_{P/Z} ≅ a_{P/Ȳ} ∘ a_{Ȳ/Z}`, restricted to `X`. -/
def compIso₁ : upperShriek (f ≫ g) (compactification f g cg cfg) ≅
    (twistedInverseImage cg.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ⋙
      twistedInverseImage (proj f g cg cfg)
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)) ⋙
      quasiCoherentDerivedPullback' (ι f g cg cfg) :=
  Functor.isoWhiskerRight (twistedInverseImageCompIso (proj f g cg cfg) cg.toBase _ _ _) _

/-- Restriction from `P` to `X` is restriction to `Q` followed by restriction to `X`, restriction
to `Q` being identified with derived pullback as a left adjoint of `R(Q ⟶ P)_*`. -/
def compIso₂ : quasiCoherentDerivedPullback' (ι f g cg cfg) ≅
    OpenImmersion.restrictedDerivedRestrict (pullback.fst (proj f g cg cfg) cg.immersion) ⋙
      quasiCoherentDerivedPullback' (restrictι f g cg cfg) :=
  quasiCoherentDerivedPullbackCongr (pullback.lift_fst _ _ _).symm ≪≫
    (quasiCoherentDerivedPullbackCompIso (restrictι f g cg cfg) (pullback.fst _ _)).symm ≪≫
    Functor.isoWhiskerRight (restrictedDerivedRestrictAdjointIso
      (pullback.fst (proj f g cg cfg) cg.immersion)).symm _

/-- Restriction to `Y ⊆ Ȳ` is derived pullback along `Y ⟶ Ȳ`, as left adjoints of `R(Y ⟶ Ȳ)_*`. -/
def compIso₃ :
    OpenImmersion.restrictedDerivedRestrict cg.immersion ⋙
        twistedInverseImage (pullback.snd (proj f g cg cfg) cg.immersion)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ⋙
        quasiCoherentDerivedPullback' (restrictι f g cg cfg) ≅
      quasiCoherentDerivedPullback' cg.immersion ⋙
        twistedInverseImage (pullback.snd (proj f g cg cfg) cg.immersion)
          (isQuasicoherent_homology_derivedPushforward_of_qcqs _) ⋙
        quasiCoherentDerivedPullback' (restrictι f g cg cfg) :=
  Functor.isoWhiskerRight (restrictedDerivedRestrictAdjointIso cg.immersion) _

/-- The twisted inverse image of `Ȳ ⟶ Z`. -/
abbrev aBase :=
  twistedInverseImage cg.toBase (isQuasicoherent_homology_derivedPushforward_of_qcqs cg.toBase)

/-- The twisted inverse image of `P ⟶ Ȳ`. -/
abbrev aProj := twistedInverseImage (proj f g cg cfg)
  (isQuasicoherent_homology_derivedPushforward_of_qcqs (proj f g cg cfg))

/-- The twisted inverse image of `Q ⟶ Y`. -/
abbrev aRes := twistedInverseImage (pullback.snd (proj f g cg cfg) cg.immersion)
  (isQuasicoherent_homology_derivedPushforward_of_qcqs _)

/-- Derived pullback along `X ⟶ Q`. -/
abbrev pullRes := quasiCoherentDerivedPullback' (restrictι f g cg cfg)

/-- Restriction from `P` to `Q`. -/
abbrev resFst :=
  OpenImmersion.restrictedDerivedRestrict (pullback.fst (proj f g cg cfg) cg.immersion)

/-- Restriction from `Ȳ` to `Y`. -/
abbrev resBase := OpenImmersion.restrictedDerivedRestrict cg.immersion

/-- The map of [Stacks, Tag 0A9L] for `Q ⊆ P`, between the composites. -/
def step₃ : aBase g cg ⋙ ((aProj f g cg cfg ⋙ resFst f g cg cfg) ⋙ pullRes f g cg cfg) ⟶
    aBase g cg ⋙ ((resBase g cg ⋙ aRes f g cg cfg) ⋙ pullRes f g cg cfg) :=
  Functor.whiskerLeft (aBase g cg)
    (Functor.whiskerRight (restrictionMap f g cg cfg) (pullRes f g cg cfg))

/-- `g^! ∘ f^!` at `cg` and `Q`, unfolded. -/
def tgtIso : upperShriek g cg ⋙ upperShriek f (restrictCompactification f g cg cfg) ≅
    aBase g cg ⋙
      (quasiCoherentDerivedPullback' cg.immersion ⋙ aRes f g cg cfg ⋙ pullRes f g cg cfg) :=
  Iso.refl _

/-- `(f ≫ g)^!` at `P`, unfolded through `Q`. -/
def srcIso : upperShriek (f ≫ g) (compactification f g cg cfg) ≅
    aBase g cg ⋙ ((aProj f g cg cfg ⋙ resFst f g cg cfg) ⋙ pullRes f g cg cfg) :=
  compIso₁ f g cg cfg ≪≫ Functor.isoWhiskerLeft _ (compIso₂ f g cg cfg) ≪≫
    Functor.associator _ _ _ ≪≫
    Functor.isoWhiskerLeft (aBase g cg) ((Functor.associator _ _ _).symm)

/-- From the target of `step₃` to `g^! ∘ f^!`. -/
def midIso : aBase g cg ⋙ ((resBase g cg ⋙ aRes f g cg cfg) ⋙ pullRes f g cg cfg) ≅
    upperShriek g cg ⋙ upperShriek f (restrictCompactification f g cg cfg) :=
  Functor.isoWhiskerLeft (aBase g cg) (Functor.associator _ _ _ ≪≫ compIso₃ f g cg cfg) ≪≫
    (tgtIso f g cg cfg).symm

/-- **The comparison `(f ≫ g)^! ⟶ f^! ∘ g^!` at the compactifications `P` and `Q`.** It is
`a_{P/Z} ≅ a_{P/Ȳ} ∘ a_{Ȳ/Z}`, restricted to `X` through `Q`, followed by the map of
[Stacks, Tag 0A9L] for the square `Q ⊆ P` over `Y ⊆ Ȳ`; every other factor is an isomorphism. -/
def upperShriekCompHom :
    upperShriek (f ≫ g) (compactification f g cg cfg) ⟶
      upperShriek g cg ⋙ upperShriek f (restrictCompactification f g cg cfg) :=
  (srcIso f g cg cfg).hom ≫ step₃ f g cg cfg ≫ (midIso f g cg cfg).hom

/-- `upperShriekCompHom` is invertible at `K` wherever the map of [Stacks, Tag 0A9L] for `Q ⊆ P`
is invertible at `ā_{Ȳ}(K)`. -/
instance isIso_upperShriekCompHom_app (K : quasiCoherentDerivedCategory Z.left)
    [hK : IsIso ((restrictionMap f g cg cfg).app ((aBase g cg).obj K))] :
    IsIso ((upperShriekCompHom f g cg cfg).app K) := by
  have : IsIso ((step₃ f g cg cfg).app K) :=
    inferInstanceAs (IsIso ((pullRes f g cg cfg).map
      ((restrictionMap f g cg cfg).app ((aBase g cg).obj K))))
  simp only [upperShriekCompHom, NatTrans.comp_app]
  infer_instance

/-- **`(f ≫ g)^! K ≅ f^!(g^! K)` at the compactifications `P` and `Q`**, wherever the map of
[Stacks, Tag 0A9L] for `Q ⊆ P` over `Y ⊆ Ȳ` is invertible at `ā_{Ȳ}(K)`. -/
def upperShriekObjIso (K : quasiCoherentDerivedCategory Z.left)
    [IsIso ((restrictionMap f g cg cfg).app ((twistedInverseImage cg.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs cg.toBase)).obj K))] :
    (upperShriek (f ≫ g) (compactification f g cg cfg)).obj K ≅
      (upperShriek f (restrictCompactification f g cg cfg)).obj ((upperShriek g cg).obj K) :=
  asIso ((upperShriekCompHom f g cg cfg).app K)

/-! ### The composition isomorphism, wherever the maps of Tag 0A9L are invertible -/

open DominatingCompactification in
/-- **`(f ≫ g)^! K ≅ f^!(g^! K)` for arbitrary compactifications** `cf`, `cg`, `cfg`, wherever the
five maps of [Stacks, Tag 0A9L] involved are invertible: the comparison of `cfg` with `P`
(`Stacks.Duality.DominatingCompactification.upperShriekObjIsoOfIsIso`), the passage from `P` to
`Q` (`upperShriekObjIso`), and the comparison of `Q` with `cf` at `g^! K`. This is the content of
[Stacks, Tag 0ATX], with independence of the compactifications ([Stacks, Tag 0AA0]) built in;
[Stacks, Tag 0A9P] supplies the invertibility on `D⁺_QCoh`. -/
def upperShriekCompObjIsoOfIsIso (cf : CompactificationOf (Over.mk f.left))
    (K : quasiCoherentDerivedCategory Z.left)
    [IsIso ((restrictionMapFst (f ≫ g) cfg (compactification f g cg cfg)).app
      ((twistedInverseImage cfg.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs cfg.toBase)).obj K))]
    [IsIso ((restrictionMapSnd (f ≫ g) cfg (compactification f g cg cfg)).app
      ((twistedInverseImage (compactification f g cg cfg).toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj K))]
    [IsIso ((restrictionMap f g cg cfg).app ((twistedInverseImage cg.toBase
      (isQuasicoherent_homology_derivedPushforward_of_qcqs cg.toBase)).obj K))]
    [IsIso ((restrictionMapFst f (restrictCompactification f g cg cfg) cf).app
      ((twistedInverseImage (restrictCompactification f g cg cfg).toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs _)).obj ((upperShriek g cg).obj K)))]
    [IsIso ((restrictionMapSnd f (restrictCompactification f g cg cfg) cf).app
      ((twistedInverseImage cf.toBase
        (isQuasicoherent_homology_derivedPushforward_of_qcqs cf.toBase)).obj
          ((upperShriek g cg).obj K)))] :
    (upperShriek (f ≫ g) cfg).obj K ≅ (upperShriek f cf).obj ((upperShriek g cg).obj K) :=
  upperShriekObjIsoOfIsIso (f ≫ g) cfg (compactification f g cg cfg) K ≪≫
    upperShriekObjIso f g cg cfg K ≪≫
    upperShriekObjIsoOfIsIso f (restrictCompactification f g cg cfg) cf _

end Stacks.Duality.CompCompactification

end
