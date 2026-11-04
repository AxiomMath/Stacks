module

public import StacksFrontier.AlgebraicGeometry.Descent.FrobeniusColimitVectorBundleFibration

/-!
# Sheaves of modules over a system of sheaves of rings on the big h site

A *system of sheaves of rings* on the big h category over `S` assigns to every object `U` a sheaf
of rings `𝓡 U` on the opens of the underlying scheme of `U`, and to every arrow `f : V ⟶ U` a
morphism of sheaves of rings `𝓡 U ⟶ f_* (𝓡 V)`, strictly compatible with identities and
composition. Extension of scalars along these morphisms makes the categories of sheaves of
`𝓡 U`-modules into a pseudofunctor on the big h category, exactly as the Frobenius colimits
`colim_F 𝒪_U` do for Stacks Tag 0EXE.

The point of the abstraction is the Zariski stack condition of
`StacksFrontier/AlgebraicGeometry/Descent/BigHRingSheafSystemZariski.lean`: it is proved once, for an
arbitrary system, so that no statement of it has to elaborate the sequential colimit that defines
`colim_F 𝒪_U`. The pseudofunctor of all Frobenius-colimit modules of Stacks Tag 0EXE,
`AlgebraicGeometry.frobeniusColimitModulePseudofunctor`, is the pseudofunctor of one such system,
`AlgebraicGeometry.frobeniusRingSheafSystem`, **on the nose**
(`AlgebraicGeometry.frobeniusColimitModulePseudofunctor_eq`).

## Main definitions

* `AlgebraicGeometry.BigHOver.RingSheafSystem`: a system of sheaves of rings on the big h category
  over `S`.
* `AlgebraicGeometry.BigHOver.RingSheafSystem.pullbackIdOfEq` and
  `AlgebraicGeometry.BigHOver.RingSheafSystem.pullbackCompOfEq`: the identity and composition
  comparisons of extension of scalars, with the morphisms of sheaves of rings as parameters.
* `AlgebraicGeometry.BigHOver.RingSheafSystem.modulePseudofunctor`: the pseudofunctor of sheaves
  of modules of a system.
* `AlgebraicGeometry.frobeniusRingSheafSystem`: the system of the Frobenius colimits of the
  structure sheaves.

## Main results

* `AlgebraicGeometry.frobeniusColimitModulePseudofunctor_eq`: the pseudofunctor of all
  Frobenius-colimit modules is the pseudofunctor of the Frobenius system.

## Implementation notes

The comparisons and their coherences are those of
`StacksFrontier/AlgebraicGeometry/Descent/FrobeniusColimitFunctorial.lean`, read at an arbitrary
family of sheaves of rings; the proofs there never used that the sheaves of rings are Frobenius
colimits. They are restated here, rather than the Frobenius ones being reused, because the
Frobenius ones are typed at `AlgebraicGeometry.frobeniusColimitRingSheaf`, and a statement about
an arbitrary system cannot be phrased through them. The definitions are written in exactly the
shape of the Frobenius ones, which is what makes
`AlgebraicGeometry.frobeniusColimitModulePseudofunctor_eq` hold by `rfl`.

## References

* [Stacks Project, Tag 0EXE](https://stacks.math.columbia.edu/tag/0EXE)
-/

@[expose] public noncomputable section

open CategoryTheory CategoryTheory.Limits Opposite TopologicalSpace
open Stacks.Frobenius

namespace AlgebraicGeometry

universe u

namespace Scheme

variable {X Y Z W : Scheme.{u}}

/-- Extension of scalars along a morphism **equal to** an identity of sheaves of rings is the
identity functor. This is `AlgebraicGeometry.frobeniusColimitPullbackIdOfEq` at an arbitrary sheaf
of rings. -/
noncomputable def ringPullbackIdOfEq (X : Scheme.{u})
    (R : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u})
    (d : R ⟶ ((𝟙 X : X ⟶ X).ringSheafPushforward).obj R) (hd : d = 𝟙 R) :
    SheafOfModules.pullback.{u} d ≅ 𝟭 (SheafOfModules.{u} R) :=
  eqToIso (congrArg (fun φ => SheafOfModules.pullback.{u} φ) hd) ≪≫
    SheafOfModules.pullbackId.{u} R

/-- Extension of scalars along two morphisms of sheaves of rings is extension of scalars along a
morphism **equal to** their composite. This is `AlgebraicGeometry.frobeniusColimitPullbackCompOfEq`
at arbitrary sheaves of rings. -/
noncomputable def ringPullbackCompOfEq (f : X ⟶ Y) (g : Y ⟶ Z)
    {RX : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}}
    {RY : Sheaf (Opens.grothendieckTopology (Y : TopCat)) RingCat.{u}}
    {RZ : Sheaf (Opens.grothendieckTopology (Z : TopCat)) RingCat.{u}}
    (a : RZ ⟶ (g.ringSheafPushforward).obj RY) (b : RY ⟶ (f.ringSheafPushforward).obj RX)
    (c : RZ ⟶ ((f ≫ g).ringSheafPushforward).obj RX)
    (hc : c = a ≫ (g.ringSheafPushforward).map b) :
    SheafOfModules.pullback.{u} a ⋙ SheafOfModules.pullback.{u} b ≅
      SheafOfModules.pullback.{u} c :=
  SheafOfModules.pullbackComp.{u} a b ≪≫
    eqToIso (congrArg (fun φ => SheafOfModules.pullback.{u} φ) hc.symm)

/-- At the defining equation `c = a ≫ g_* b` itself, the composition comparison
`AlgebraicGeometry.Scheme.ringPullbackCompOfEq` is `SheafOfModules.pullbackComp`. -/
lemma ringPullbackCompOfEq_self (f : X ⟶ Y) (g : Y ⟶ Z)
    {RX : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}}
    {RY : Sheaf (Opens.grothendieckTopology (Y : TopCat)) RingCat.{u}}
    {RZ : Sheaf (Opens.grothendieckTopology (Z : TopCat)) RingCat.{u}}
    (a : RZ ⟶ (g.ringSheafPushforward).obj RY) (b : RY ⟶ (f.ringSheafPushforward).obj RX) :
    ringPullbackCompOfEq f g a b _ rfl = SheafOfModules.pullbackComp.{u} a b := by
  simp only [ringPullbackCompOfEq]
  exact Iso.trans_refl _

/-- At the identity morphism `𝟙 R` itself, the identity comparison
`AlgebraicGeometry.Scheme.ringPullbackIdOfEq` is `SheafOfModules.pullbackId`. -/
lemma ringPullbackIdOfEq_self (X : Scheme.{u})
    (R : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}) :
    ringPullbackIdOfEq X R (𝟙 R) rfl = SheafOfModules.pullbackId.{u} R := by
  simp only [ringPullbackIdOfEq]
  exact Iso.refl_trans _

/-- The associativity pentagon of `AlgebraicGeometry.Scheme.ringPullbackCompOfEq`. -/
lemma ringPullbackCompOfEq_assoc (f : X ⟶ Y) (g : Y ⟶ Z) (h : Z ⟶ W)
    {RX : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}}
    {RY : Sheaf (Opens.grothendieckTopology (Y : TopCat)) RingCat.{u}}
    {RZ : Sheaf (Opens.grothendieckTopology (Z : TopCat)) RingCat.{u}}
    {RW : Sheaf (Opens.grothendieckTopology (W : TopCat)) RingCat.{u}}
    (a : RW ⟶ (h.ringSheafPushforward).obj RZ) (b : RZ ⟶ (g.ringSheafPushforward).obj RY)
    (c : RY ⟶ (f.ringSheafPushforward).obj RX)
    (ab : RW ⟶ ((g ≫ h).ringSheafPushforward).obj RY)
    (hab : ab = a ≫ (h.ringSheafPushforward).map b)
    (bc : RZ ⟶ ((f ≫ g).ringSheafPushforward).obj RX)
    (hbc : bc = b ≫ (g.ringSheafPushforward).map c)
    (d : RW ⟶ ((f ≫ g ≫ h).ringSheafPushforward).obj RX)
    (hd : d = a ≫ (h.ringSheafPushforward).map bc)
    (hd' : d = ab ≫ ((g ≫ h).ringSheafPushforward).map c) :
    Functor.isoWhiskerLeft (SheafOfModules.pullback.{u} a)
          (ringPullbackCompOfEq f g b c bc hbc) ≪≫
        ringPullbackCompOfEq (f ≫ g) h a bc d hd =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (ringPullbackCompOfEq g h a b ab hab)
            (SheafOfModules.pullback.{u} c) ≪≫
          ringPullbackCompOfEq f (g ≫ h) ab c d hd' := by
  subst hab
  subst hbc
  subst hd
  simp only [ringPullbackCompOfEq_self]
  exact SheafOfModules.pullback_assoc.{u} a b c

/-- The left unit coherence of `AlgebraicGeometry.Scheme.ringPullbackCompOfEq`. -/
lemma ringPullbackIdOfEq_comp (f : X ⟶ Y)
    {RX : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}}
    {RY : Sheaf (Opens.grothendieckTopology (Y : TopCat)) RingCat.{u}}
    (e : RY ⟶ ((𝟙 Y : Y ⟶ Y).ringSheafPushforward).obj RY) (he : e = 𝟙 RY)
    (b : RY ⟶ (f.ringSheafPushforward).obj RX)
    (c : RY ⟶ ((f ≫ 𝟙 Y).ringSheafPushforward).obj RX)
    (hc : c = e ≫ ((𝟙 Y : Y ⟶ Y).ringSheafPushforward).map b)
    (hFE : SheafOfModules.pullback.{u} c = SheafOfModules.pullback.{u} b) :
    ringPullbackCompOfEq f (𝟙 Y) e b c hc ≪≫ eqToIso hFE =
      Functor.isoWhiskerRight (ringPullbackIdOfEq Y RY e he)
          (SheafOfModules.pullback.{u} b) ≪≫
        Functor.leftUnitor _ := by
  subst he
  subst hc
  rw [ringPullbackIdOfEq_self]
  refine (Iso.trans_refl _).trans ?_
  exact (ringPullbackCompOfEq_self f (𝟙 Y) _ b).trans
    (SheafOfModules.pullback_id_comp.{u} b)

/-- The right unit coherence of `AlgebraicGeometry.Scheme.ringPullbackCompOfEq`. -/
lemma ringPullbackCompOfEq_id (f : X ⟶ Y)
    {RX : Sheaf (Opens.grothendieckTopology (X : TopCat)) RingCat.{u}}
    {RY : Sheaf (Opens.grothendieckTopology (Y : TopCat)) RingCat.{u}}
    (e : RX ⟶ ((𝟙 X : X ⟶ X).ringSheafPushforward).obj RX) (he : e = 𝟙 RX)
    (a : RY ⟶ (f.ringSheafPushforward).obj RX)
    (c : RY ⟶ ((𝟙 X ≫ f).ringSheafPushforward).obj RX)
    (hc : c = a ≫ (f.ringSheafPushforward).map e)
    (hFE : SheafOfModules.pullback.{u} c = SheafOfModules.pullback.{u} a) :
    ringPullbackCompOfEq (𝟙 X) f a e c hc ≪≫ eqToIso hFE =
      Functor.isoWhiskerLeft (SheafOfModules.pullback.{u} a)
          (ringPullbackIdOfEq X RX e he) ≪≫
        Functor.rightUnitor _ := by
  subst he
  subst hc
  rw [ringPullbackIdOfEq_self]
  refine (Iso.trans_refl _).trans ?_
  exact (ringPullbackCompOfEq_self (𝟙 X) f a _).trans
    (SheafOfModules.pullback_comp_id.{u} a)

end Scheme

namespace BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)

/-- **A system of sheaves of rings on the big h category over `S`**: a sheaf of rings on the opens
of the underlying scheme of every object, and for every arrow `f : V ⟶ U` a morphism of sheaves
of rings `𝓡 U ⟶ f_* (𝓡 V)`, strictly compatible with identities and composition. -/
structure RingSheafSystem where
  /-- The sheaf of rings on an object. -/
  ring (U : BigHOver B S hS) :
    Sheaf (Opens.grothendieckTopology (((toScheme B S hS).obj U) : TopCat)) RingCat.{u}
  /-- The morphism of sheaves of rings attached to an arrow. -/
  hom {V U : BigHOver B S hS} (f : V ⟶ U) :
    ring U ⟶ (((toScheme B S hS).map f).ringSheafPushforward).obj (ring V)
  /-- The morphism attached to an identity arrow is the identity. -/
  hom_id (U : BigHOver B S hS) : hom (𝟙 U) = 𝟙 (ring U)
  /-- The morphism attached to a composite `f ≫ g` is the morphism of `g` followed by the
  pushforward along `g` of the morphism of `f`. -/
  hom_comp {W V U : BigHOver B S hS} (f : W ⟶ V) (g : V ⟶ U) :
    hom (f ≫ g) = hom g ≫ (((toScheme B S hS).map g).ringSheafPushforward).map (hom f)

namespace RingSheafSystem

variable {B S hS} (𝓡 : RingSheafSystem B S hS)

/-- The transition functor of a system of sheaves of rings along an arrow of the opposite of the
big h category: extension of scalars. -/
abbrev pull {V U : (BigHOver B S hS)ᵒᵖ} (f : V ⟶ U) :
    SheafOfModules.{u} (𝓡.ring V.unop) ⥤ SheafOfModules.{u} (𝓡.ring U.unop) :=
  SheafOfModules.pullback.{u} (𝓡.hom f.unop)

/-- The composition comparison of the transition functors. -/
abbrev pullComp {W V U : (BigHOver B S hS)ᵒᵖ} (f : W ⟶ V) (g : V ⟶ U) :
    𝓡.pull f ⋙ 𝓡.pull g ≅ 𝓡.pull (f ≫ g) :=
  Scheme.ringPullbackCompOfEq ((toScheme B S hS).map g.unop) ((toScheme B S hS).map f.unop)
    (𝓡.hom f.unop) (𝓡.hom g.unop) (𝓡.hom (f ≫ g).unop) (𝓡.hom_comp g.unop f.unop)

/-- The identity comparison of the transition functors. -/
abbrev pullId (U : (BigHOver B S hS)ᵒᵖ) : 𝓡.pull (𝟙 U) ≅ 𝟭 _ :=
  Scheme.ringPullbackIdOfEq ((toScheme B S hS).obj U.unop) (𝓡.ring U.unop)
    (𝓡.hom (𝟙 U).unop) (𝓡.hom_id U.unop)

/-- The associativity coherence of the composition comparisons
`AlgebraicGeometry.BigHOver.RingSheafSystem.pullComp`. -/
lemma pullComp_assoc {b₀ b₁ b₂ b₃ : (BigHOver B S hS)ᵒᵖ}
    (f : b₀ ⟶ b₁) (g : b₁ ⟶ b₂) (h : b₂ ⟶ b₃) :
    Functor.isoWhiskerLeft (𝓡.pull f) (𝓡.pullComp g h) ≪≫ 𝓡.pullComp f (g ≫ h) =
      (Functor.associator _ _ _).symm ≪≫
        Functor.isoWhiskerRight (𝓡.pullComp f g) (𝓡.pull h) ≪≫ 𝓡.pullComp (f ≫ g) h :=
  Scheme.ringPullbackCompOfEq_assoc
    ((toScheme B S hS).map h.unop) ((toScheme B S hS).map g.unop)
    ((toScheme B S hS).map f.unop)
    (𝓡.hom f.unop) (𝓡.hom g.unop) (𝓡.hom h.unop)
    (𝓡.hom (f ≫ g).unop) (𝓡.hom_comp g.unop f.unop)
    (𝓡.hom (g ≫ h).unop) (𝓡.hom_comp h.unop g.unop)
    (𝓡.hom (f ≫ g ≫ h).unop) (𝓡.hom_comp (g ≫ h).unop f.unop)
    (𝓡.hom_comp h.unop (f ≫ g).unop)

/-- The left unit coherence of the comparisons
`AlgebraicGeometry.BigHOver.RingSheafSystem.pullId` and
`AlgebraicGeometry.BigHOver.RingSheafSystem.pullComp`. -/
lemma pullId_comp {b₀ b₁ : (BigHOver B S hS)ᵒᵖ} (f : b₀ ⟶ b₁) :
    𝓡.pullComp (𝟙 b₀) f ≪≫
        eqToIso (congrArg (fun x : b₀ ⟶ b₁ => 𝓡.pull x) (Category.id_comp f)) =
      Functor.isoWhiskerRight (𝓡.pullId b₀) (𝓡.pull f) ≪≫ Functor.leftUnitor _ :=
  Scheme.ringPullbackIdOfEq_comp ((toScheme B S hS).map f.unop)
    (𝓡.hom (𝟙 b₀).unop) (𝓡.hom_id b₀.unop) (𝓡.hom f.unop) (𝓡.hom (𝟙 b₀ ≫ f).unop)
    (𝓡.hom_comp f.unop (𝟙 b₀).unop)
    (congrArg (fun x : b₀ ⟶ b₁ => 𝓡.pull x) (Category.id_comp f))

/-- The right unit coherence of the comparisons
`AlgebraicGeometry.BigHOver.RingSheafSystem.pullComp` and
`AlgebraicGeometry.BigHOver.RingSheafSystem.pullId`. -/
lemma pullComp_id {b₀ b₁ : (BigHOver B S hS)ᵒᵖ} (f : b₀ ⟶ b₁) :
    𝓡.pullComp f (𝟙 b₁) ≪≫
        eqToIso (congrArg (fun x : b₀ ⟶ b₁ => 𝓡.pull x) (Category.comp_id f)) =
      Functor.isoWhiskerLeft (𝓡.pull f) (𝓡.pullId b₁) ≪≫ Functor.rightUnitor _ :=
  Scheme.ringPullbackCompOfEq_id ((toScheme B S hS).map f.unop)
    (𝓡.hom (𝟙 b₁).unop) (𝓡.hom_id b₁.unop) (𝓡.hom f.unop) (𝓡.hom (f ≫ 𝟙 b₁).unop)
    (𝓡.hom_comp (𝟙 b₁).unop f.unop)
    (congrArg (fun x : b₀ ⟶ b₁ => 𝓡.pull x) (Category.comp_id f))

/-- **The pseudofunctor of sheaves of modules of a system of sheaves of rings.** It sends an
object `U` of the big h category over `S` to the category of sheaves of `𝓡 U`-modules and an
arrow to extension of scalars. -/
def modulePseudofunctor :
    Pseudofunctor (LocallyDiscrete (BigHOver B S hS)ᵒᵖ) Cat.{u, u + 1} :=
  LocallyDiscrete.mkPseudofunctor
    (fun U => Cat.of (SheafOfModules.{u} (𝓡.ring U.unop)))
    (fun {_ _} f => Functor.toCatHom (𝓡.pull f))
    (fun U => Cat.Hom.isoMk (𝓡.pullId U))
    (fun {_ _ _} f g => Cat.Hom.isoMk (𝓡.pullComp f g).symm)
    (fun {_ _ _ _} f g h =>
      Cat.map₂_associator_of_pentagon _ _ _ _ _ _ _ _ _ _ (𝓡.pullComp_assoc f g h))
    (fun {b₀ b₁} f =>
      Cat.map₂_left_unitor_of_unit (𝓡.pull (𝟙 b₀)) (𝓡.pull f) (𝓡.pull (𝟙 b₀ ≫ f))
        (𝓡.pullId b₀) (𝓡.pullComp (𝟙 b₀) f)
        (congrArg (fun x : b₀ ⟶ b₁ => 𝓡.pull x) (Category.id_comp f))
        (𝓡.pullId_comp f))
    (fun {b₀ b₁} f =>
      Cat.map₂_right_unitor_of_unit (𝓡.pull f) (𝓡.pull (f ≫ 𝟙 b₁)) (𝓡.pull (𝟙 b₁))
        (𝓡.pullId b₁) (𝓡.pullComp f (𝟙 b₁))
        (congrArg (fun x : b₀ ⟶ b₁ => 𝓡.pull x) (Category.comp_id f))
        (𝓡.pullComp_id f))

end RingSheafSystem

end BigHOver

variable (B : BigHSite.{u}) (S : Scheme.{u}) (hS : B.Contains S) (p : ℕ) [Fact p.Prime]
  (hpS : IsInCharacteristic S p)

/-- **The system of Frobenius colimits of the structure sheaves** on the big h category over a
scheme `S` in characteristic `p`: `U ↦ colim_F 𝒪_U`, with the canonical morphisms of Frobenius
colimits. -/
def frobeniusRingSheafSystem : BigHOver.RingSheafSystem B S hS where
  ring U := bigHFrobeniusColimitRingSheaf B S hS p hpS U
  hom f := bigHFrobeniusColimitHom B S hS p hpS f.op
  hom_id _ := frobeniusColimitStructureSheafHom_id _ p _
  hom_comp _ _ := frobeniusColimitStructureSheafHom_comp p _ _ _ _ _

/-- **The pseudofunctor of all Frobenius-colimit modules is the pseudofunctor of the Frobenius
system of sheaves of rings**, on the nose. -/
theorem frobeniusColimitModulePseudofunctor_eq :
    frobeniusColimitModulePseudofunctor B S hS p hpS =
      (frobeniusRingSheafSystem B S hS p hpS).modulePseudofunctor :=
  rfl

end AlgebraicGeometry

end
