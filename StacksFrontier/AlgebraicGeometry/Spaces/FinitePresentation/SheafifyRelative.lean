module

public import Mathlib.CategoryTheory.Category.ULift
public import Mathlib.CategoryTheory.Sites.Equivalence
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import Mathlib.CategoryTheory.Sites.Over
public import Mathlib.CategoryTheory.Sites.Sheafification
public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.FppfLocal
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Sheafify
public import StacksFrontier.AlgebraicGeometry.Spaces.FinitePresentation.Transport
public import StacksFrontier.CategoryTheory.Sites.Localization.SheavesOverRepresentable
public import StacksFrontier.CategoryTheory.Sites.Sheafification.SectionsLocalDescription
public import StacksFrontier.CategoryTheory.Sites.Sheafification.PreservesFiniteLimits

/-!
# Relative limit preservation under fppf sheafification

Sheafifying a relatively limit-preserving transformation of presheaves of sets on the big
fppf site over a scheme gives a relatively limit-preserving transformation of the
associated sheaves.

## Main results

* `AlgebraicGeometry.relativelyLimitPreserving_sheafifyMap` is preservation of relative
  limit preservation under fppf sheafification.

## Implementation notes

Relative limit preservation is tested on the section fibres of Tag 049J, and the section
fibre of the sheafified transformation over a section of the sheafified target is the
sheafification of the section fibre of the original: the comparison map is locally
bijective, so it becomes an isomorphism after sheafifying. Identifying the slice of the
slice with a single slice then reduces the statement to limit preservation of a
sheafification, which is `AlgebraicGeometry.limitPreserving_sheafify`, applied over the
members of an fppf covering on which the chosen target section comes from the presheaf, and
assembled by `AlgebraicGeometry.limitPreserving_of_fppfCover`.

The universes of the tested index objects and morphisms are bounded by the scheme universe,
which expresses the ambient set-sized limits in the source; limits in a smaller category of
schemes do not suffice for covering descent. The universe of sets is at least the object
universe of the site, as required by the available sheafification construction.

## References

* [Stacks Project, Tag 049Q](https://stacks.math.columbia.edu/tag/049Q)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits

universe u v w w' z z' zC zD

namespace AlgebraicGeometry

/-- The unit of sheafification is locally surjective and locally injective in the value
universe used here, obtained by transporting along the equivalence with the hom-lifted site. -/
private theorem toSheafify_isLocallyBijective_large
    {C : Type (u + 1)} [Category.{u} C]
    (J : GrothendieckTopology C)
    (P : Cᵒᵖ ⥤ Type (max (u + 1) v)) :
    Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P) ∧
      Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P) := by
  let e : C ≌ ULiftHom.{max (u + 1) v} C := ULiftHom.equiv
  let K := e.inverse.inducedTopology J
  have : e.functor.IsContinuous J K := by
    dsimp [K]
    infer_instance
  have : e.functor.IsCocontinuous J K := by
    dsimp [K]
    infer_instance
  let P' : (ULiftHom.{max (u + 1) v} C)ᵒᵖ ⥤ Type (max (u + 1) v) :=
    e.inverse.op ⋙ P
  let αP := (sheafToPresheaf J (Type (max (u + 1) v))).mapIso
    ((e.functor.pushforwardContinuousSheafificationCompatibility (Type (max (u + 1) v)) J K).app P')
  have hunit : CategoryTheory.toSheafify J P ≫ αP.hom =
      Functor.whiskerLeft e.functor.op (CategoryTheory.toSheafify K P') :=
    e.functor.toSheafify_pullbackSheafificationCompatibility (Type (max (u + 1) v)) J K P'
  have h : Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J P ≫ αP.hom) ∧
      Presheaf.IsLocallyInjective J (CategoryTheory.toSheafify J P ≫ αP.hom) :=
    hunit ▸ ⟨Presheaf.isLocallySurjective_whisker J K e.functor (CategoryTheory.toSheafify K P'),
      Presheaf.isLocallyInjective_whisker J K e.functor (CategoryTheory.toSheafify K P')⟩
  have := h.1
  have := h.2
  have : Presheaf.IsLocallyInjective J αP.hom :=
    Presheaf.isLocallyInjective_of_injective J _ fun X =>
      ((ConcreteCategory.isIso_iff_bijective _).1 inferInstance).1
  exact ⟨@Presheaf.isLocallySurjective_of_isLocallySurjective_of_isLocallyInjective
      _ _ J _ _ _ _ _ _ _ _ _ _ αP.hom ‹_› this,
    Presheaf.isLocallyInjective_of_isLocallyInjective J _ αP.hom⟩

/-- A section of a sheafification over an object of the big fppf site over `S` comes, on an
fppf covering of that object, from a section of the presheaf. -/
private theorem exists_fppf_local_sections
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v)}
    (X : BigFppfOver B S hS)
    (y : (sheafify (BigFppfOver.topology B S hS) G).obj
      (Opposite.op X)) :
    ∃ E : PreZeroHypercover X.left, IsFppfCovering ⟨X.left, E⟩ ∧
      ∀ i : E.I₀, ∃ (Y : BigFppfOver B S hS) (f : Y ⟶ X)
          (yᵢ : G.obj (Opposite.op Y)) (hY : Y.left = E.X i),
        (Over.forget (B.obj hS)).map f = eqToHom hY ≫ E.f i ∧
          (sheafify (BigFppfOver.topology B S hS) G).map f.op y =
            (CategoryTheory.toSheafify
              (BigFppfOver.topology B S hS) G).app (Opposite.op Y) yᵢ := by
  let J := BigFppfOver.topology B S hS
  have : Presheaf.IsLocallySurjective J (CategoryTheory.toSheafify J G) :=
    (toSheafify_isLocallyBijective_large J G).1
  let R : Sieve X := Presheaf.imageSieve (CategoryTheory.toSheafify J G) y
  have hR : R ∈ J X := Presheaf.imageSieve_mem (J := J)
    (f := CategoryTheory.toSheafify J G) (s := y)
  have hR' : (Sieve.overEquiv X) R ∈ B.topology X.left := by
    simpa [BigFppfOver.topology, BigFppfOver] using
      (GrothendieckTopology.mem_over_iff B.topology R).mp hR
  obtain ⟨E, hE, hRef⟩ := AlgebraicGeometry.Space.exists_covering_refining_sieve B hR'
  refine ⟨E, B.isFppfCovering_of_isCovering hE, ?_⟩
  intro i
  have hbase : ((Sieve.overEquiv X) R).arrows (E.f i) :=
    (Presieve.ofArrows_le_iff.mp hRef) i
  have hmap : Presieve.map (Over.forget (B.obj hS)) R.arrows (E.f i) := by
    simpa [Sieve.overEquiv_apply] using hbase
  obtain ⟨Y, hY, f, hf, hmap⟩ := Presieve.map_iff.mp hmap
  change ∃ yᵢ : G.obj (Opposite.op Y),
    (CategoryTheory.toSheafify J G).app (Opposite.op Y) yᵢ =
      (sheafify J G).map f.op y at hf
  obtain ⟨yᵢ, hyᵢ⟩ := hf
  exact ⟨Y, f, yᵢ, hY, hmap, hyᵢ.symm⟩

/-- The underlying section of a point of a section fibre. -/
private def sectionFiber_val
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (X : BigFppfOver B S hS) (y : G.obj (Opposite.op X)) :
    sectionFiber B S hS a X y ⟶ (Over.forget X).op ⋙ F where
  app _W := ↾fun x => x.1
  naturality _ _ _ := rfl

/-- The section fibre of a transformation of fppf sheaves is a sheaf for the localized
topology. -/
private theorem sectionFiber_isSheaf
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type v}
    (a : F ⟶ G) (X : BigFppfOver B S hS)
    (y : G.obj (Opposite.op X))
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G) :
    Presieve.IsSheaf ((BigFppfOver.topology B S hS).over X)
      (sectionFiber B S hS a X y) := by
  let J := BigFppfOver.topology B S hS
  have hF' : Presieve.IsSheaf (J.over X) ((Over.forget X).op ⋙ F) :=
    (Over.forget X).op_comp_isSheaf_of_types (J.over X) J ⟨F, hF⟩
  have hG' : Presieve.IsSheaf (J.over X) ((Over.forget X).op ⋙ G) :=
    (Over.forget X).op_comp_isSheaf_of_types (J.over X) J ⟨G, hG⟩
  intro W R hR x hx
  obtain ⟨t, ht, htu⟩ := hF' R hR
    (x.map (sectionFiber_val B S hS a X y))
    (hx.map (sectionFiber_val B S hS a X y))
  have hmem : a.app (Opposite.op W.left) t =
      G.map W.hom.op y := by
    apply (hG'.isSeparated R hR).ext
    intro Y f hf
    show G.map f.left.op (a.app (Opposite.op W.left) t) =
      G.map f.left.op (G.map W.hom.op y)
    have hglue := ht f hf
    change F.map f.left.op t = (x f hf).1 at hglue
    rw [← NatTrans.naturality_apply a f.left.op t, hglue, (x f hf).2]
    symm
    calc
      G.map f.left.op (G.map W.hom.op y) =
          G.map (W.hom.op ≫ f.left.op) y := by rw [Functor.map_comp_apply]
      _ = G.map Y.hom.op y := by rw [← op_comp, f.w]
  refine ⟨⟨t, hmem⟩, fun Y f hf => Subtype.ext (ht f hf), ?_⟩
  intro z hz
  exact Subtype.ext (htu z.1 (fun {Y} f hf => congrArg Subtype.val (hz f hf)))

/-- Restricting a section fibre along a morphism gives the section fibre over the restricted
section. -/
private noncomputable def sectionFiber_baseChangeIso
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v)}
    (a : F ⟶ G) {X Y : BigFppfOver B S hS} (f : Y ⟶ X)
    (y : G.obj (Opposite.op X)) (z : G.obj (Opposite.op Y))
    (hz : G.map f.op y = z) :
    (Over.map f).op ⋙ sectionFiber B S hS a X y ≅
      sectionFiber B S hS a Y z := by
  refine NatIso.ofComponents (fun W => ?_) ?_
  · have hEq : G.map (W.unop.hom ≫ f).op y = G.map W.unop.hom.op z := by
      calc
        _ = G.map W.unop.hom.op (G.map f.op y) := by
          rw [← Functor.map_comp_apply, ← op_comp]
        _ = G.map W.unop.hom.op z := by rw [hz]
    exact Equiv.toIso {
      toFun := fun s => ⟨s.1, by
        change a.app (Opposite.op W.unop.left) s.1 = G.map W.unop.hom.op z
        have hs : a.app (Opposite.op W.unop.left) s.1 =
            G.map (W.unop.hom ≫ f).op y := s.2
        rw [hs, hEq]⟩
      invFun := fun s => ⟨s.1, by
        change a.app (Opposite.op W.unop.left) s.1 =
          G.map (W.unop.hom ≫ f).op y
        have hs : a.app (Opposite.op W.unop.left) s.1 =
            G.map W.unop.hom.op z := s.2
        rw [hs, ← hEq]⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }
  · intro W W' g
    ext s
    rfl

/-- Sheafification commutes with transport along an equivalence of sites which is a dense
subsite in the required sense. -/
private noncomputable def sheafify_equiv_iso
    {C : Type z} [Category.{zC, z} C] {D : Type z'} [Category.{zD, z'} D]
    (e : C ≌ D) (J : GrothendieckTopology C) (K : GrothendieckTopology D)
    [HasSheafify J (Type v)] [HasSheafify K (Type v)]
    [e.inverse.IsDenseSubsite K J]
    (P : Cᵒᵖ ⥤ Type v) :
    e.functor.op ⋙ sheafify K (e.inverse.op ⋙ P) ≅ sheafify J P :=
  (sheafToPresheaf J (Type v)).mapIso ((Adjunction.leftAdjointUniq
    (Equivalence.transportSheafificationAdjunction J K e (Type v))
    (sheafificationAdjunction J (Type v))).app P)

/-- The comparison map from the section fibre of a transformation to the section fibre of its
sheafification over the image of the chosen section. -/
private noncomputable def sectionFiber_toSheafifyMap
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v)}
    (a : F ⟶ G) (X : BigFppfOver B S hS) (y : G.obj (Opposite.op X)) :
    sectionFiber B S hS a X y ⟶
      sectionFiber B S hS
        (sheafifyMap (BigFppfOver.topology B S hS) a) X
        ((toSheafify (BigFppfOver.topology B S hS) G).app (Opposite.op X) y) where
  app W := ↾fun s => by
    refine ⟨(toSheafify (BigFppfOver.topology B S hS) F).app
      (Opposite.op W.unop.left) s.1, ?_⟩
    have hs := congrArg ((toSheafify (BigFppfOver.topology B S hS) G).app
      (Opposite.op W.unop.left)) s.2
    have hnat := congrArg (fun n => n.app (Opposite.op W.unop.left) s.1)
      (toSheafify_naturality (BigFppfOver.topology B S hS) a)
    change (sheafifyMap (BigFppfOver.topology B S hS) a).app
        (Opposite.op W.unop.left)
          ((toSheafify (BigFppfOver.topology B S hS) F).app
            (Opposite.op W.unop.left) s.1) = _
    calc
      _ = (toSheafify (BigFppfOver.topology B S hS) G).app
          (Opposite.op W.unop.left) (a.app (Opposite.op W.unop.left) s.1) := by
            simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using hnat.symm
      _ = (toSheafify (BigFppfOver.topology B S hS) G).app
          (Opposite.op W.unop.left) (G.map W.unop.hom.op y) := hs
      _ = (sheafify (BigFppfOver.topology B S hS) G).map W.unop.hom.op
          ((toSheafify (BigFppfOver.topology B S hS) G).app
            (Opposite.op X) y) := by
        rw [NatTrans.naturality_apply]
  naturality {W W'} g := by
    ext s
    apply Subtype.ext
    change (toSheafify (BigFppfOver.topology B S hS) F).app
        (Opposite.op W'.unop.left)
          (F.map g.unop.left.op s.1) =
      (sheafify (BigFppfOver.topology B S hS) F).map
        g.unop.left.op
          ((toSheafify (BigFppfOver.topology B S hS) F).app
            (Opposite.op W.unop.left) s.1)
    exact (NatTrans.naturality_apply
      (toSheafify (BigFppfOver.topology B S hS) F)
      g.unop.left.op s.1)

/-- The comparison map of section fibres is locally injective. -/
private theorem sectionFiber_toSheafifyMap_locallyInjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v)}
    (a : F ⟶ G) (X : BigFppfOver B S hS) (y : G.obj (Opposite.op X)) :
    Presheaf.IsLocallyInjective (BigFppfOver.topology B S hS |>.over X)
      (sectionFiber_toSheafifyMap B S hS a X y) := by
  let J := BigFppfOver.topology B S hS
  let j := Over.forget X
  let ηF := Functor.whiskerLeft j.op (toSheafify J F)
  have : Presheaf.IsLocallyInjective J (toSheafify J F) :=
    (toSheafify_isLocallyBijective_large J F).2
  have hηFi : Presheaf.IsLocallyInjective (J.over X) ηF :=
    Presheaf.isLocallyInjective_whisker (J.over X) J j (toSheafify J F)
  refine ⟨fun {W} p q hpq => (J.over X).superset_covering (fun _ _ hf => Subtype.ext hf)
    (hηFi.equalizerSieve_mem p.1 q.1 ?_)⟩
  simpa [sectionFiber_toSheafifyMap, ηF, j] using congrArg Subtype.val hpq

/-- The comparison map of section fibres is locally surjective. -/
private theorem sectionFiber_toSheafifyMap_locallySurjective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v)}
    (a : F ⟶ G) (X : BigFppfOver B S hS) (y : G.obj (Opposite.op X)) :
    Presheaf.IsLocallySurjective (BigFppfOver.topology B S hS |>.over X)
      (sectionFiber_toSheafifyMap B S hS a X y) := by
  let J := BigFppfOver.topology B S hS
  let j := Over.forget X
  let G' := j.op ⋙ G
  let a' := Functor.whiskerLeft j.op a
  let ηF := Functor.whiskerLeft j.op (toSheafify J F)
  let ηG := Functor.whiskerLeft j.op (toSheafify J G)
  have : Presheaf.IsLocallySurjective J (toSheafify J F) :=
    (toSheafify_isLocallyBijective_large J F).1
  have hηFs : Presheaf.IsLocallySurjective (J.over X) ηF :=
    Presheaf.isLocallySurjective_whisker (J.over X) J j (toSheafify J F)
  have : Presheaf.IsLocallyInjective J (toSheafify J G) :=
    (toSheafify_isLocallyBijective_large J G).2
  have hηGi : Presheaf.IsLocallyInjective (J.over X) ηG :=
    Presheaf.isLocallyInjective_whisker (J.over X) J j (toSheafify J G)
  refine ⟨?_⟩
  intro W q
  let R := Presheaf.imageSieve ηF q.1
  have hR : R ∈ (J.over X) W := hηFs.imageSieve_mem q.1
  let T : ∀ ⦃V : Over X⦄ (f : V ⟶ W) (_ : R f), Sieve V := fun V f hf =>
    Presheaf.equalizerSieve (F := G') (a'.app (Opposite.op V)
        (Presheaf.localPreimage ηF q.1 f hf))
      (G'.map f.op (G.map W.hom.op y))
  refine (J.over X).superset_covering ?_
    ((J.over X).transitive hR (Sieve.bind R T) ?_)
  · rintro Z k ⟨V, g, f, hf, hg, rfl⟩
    let t := Presheaf.localPreimage ηF q.1 f hf
    have ht := Presheaf.app_localPreimage ηF q.1 f hf
    have ht' : (toSheafify J F).app (Opposite.op V.left) t =
        (sheafify J F).map f.left.op q.1 := by
      simpa [ηF, j] using ht
    have hlocal := hg
    change G'.map g.op (a'.app (Opposite.op V) t) =
      G'.map g.op (G'.map f.op (G.map W.hom.op y)) at hlocal
    have hlocal' : G.map g.left.op (a.app (Opposite.op V.left) t) =
        G.map g.left.op (G.map (f.left ≫ W.hom).op y) := by
      simpa [G', a', j, ← Functor.map_comp_apply, ← op_comp] using hlocal
    have hbase : a.app (Opposite.op Z.left) (F.map g.left.op t) =
        G.map Z.hom.op y := by
      calc
        _ = G.map g.left.op (a.app (Opposite.op V.left) t) := by
          rw [NatTrans.naturality_apply]
        _ = G.map g.left.op (G.map (f.left ≫ W.hom).op y) := hlocal'
        _ = G.map (g.left ≫ (f.left ≫ W.hom)).op y := by
          rw [← Functor.map_comp_apply, ← op_comp]
        _ = G.map Z.hom.op y := by
          simp
    refine ⟨⟨F.map g.left.op t, hbase⟩, ?_⟩
    apply Subtype.ext
    show (toSheafify J F).app (Opposite.op Z.left) (F.map g.left.op t) =
      (sheafify J F).map (g.left ≫ f.left).op q.1
    calc
      _ = (sheafify J F).map g.left.op
          ((toSheafify J F).app (Opposite.op V.left) t) := by
            rw [NatTrans.naturality_apply]
      _ = (sheafify J F).map g.left.op ((sheafify J F).map f.left.op q.1) := by
            rw [ht']
      _ = (sheafify J F).map (g.left ≫ f.left).op q.1 := by
            rw [← Functor.map_comp_apply, ← op_comp]
  · intro V f hf
    apply (J.over X).superset_covering (Sieve.le_pullback_bind _ _ _ hf)
    let t := Presheaf.localPreimage ηF q.1 f hf
    have ht := Presheaf.app_localPreimage ηF q.1 f hf
    have ht' : (toSheafify J F).app (Opposite.op V.left) t =
        (sheafify J F).map f.left.op q.1 := by
      simpa [ηF, j] using ht
    have hη : (toSheafify J G).app (Opposite.op V.left)
        (a.app (Opposite.op V.left) t) =
        (toSheafify J G).app (Opposite.op V.left)
          (G.map (f.left ≫ W.hom).op y) := by
      calc
        _ = (sheafifyMap J a).app (Opposite.op V.left)
            ((toSheafify J F).app (Opposite.op V.left) t) := by
              simpa only [NatTrans.comp_app, ConcreteCategory.comp_apply] using
                congrArg (fun n => n.app (Opposite.op V.left) t)
                  (toSheafify_naturality J a)
        _ = (sheafifyMap J a).app (Opposite.op V.left)
            ((sheafify J F).map f.left.op q.1) := by
              rw [ht']
        _ = (sheafify J G).map f.left.op
            ((sheafifyMap J a).app (Opposite.op W.left) q.1) := by
              rw [NatTrans.naturality_apply]
        _ = (sheafify J G).map f.left.op
            ((sheafify J G).map W.hom.op ((toSheafify J G).app (Opposite.op X) y)) := by
              rw [q.2]
        _ = (toSheafify J G).app (Opposite.op V.left)
            (G.map (f.left ≫ W.hom).op y) := by
              rw [← Functor.map_comp_apply, ← op_comp]
              exact (NatTrans.naturality_apply (toSheafify J G)
                (f.left ≫ W.hom).op y).symm
    have hη' : ηG.app (Opposite.op V) (a'.app (Opposite.op V) t) =
        ηG.app (Opposite.op V) (G'.map f.op (G.map W.hom.op y)) := by
      show (toSheafify J G).app (Opposite.op V.left) (a.app (Opposite.op V.left) t) = _
      have hmap : G.map (f.left ≫ W.hom).op y =
          G'.map f.op (G.map W.hom.op y) := by
        simp [G', j, ← Functor.map_comp_apply, ← op_comp]
      simpa [ηG, a', j] using
        hη.trans (congrArg ((toSheafify J G).app (Opposite.op V.left)) hmap)
    exact hηGi.equalizerSieve_mem (a'.app (Opposite.op V) t)
      (G'.map f.op (G.map W.hom.op y)) hη'

/-- The sheafification of a section fibre is the section fibre of the sheafified
transformation, over the image of the chosen section. -/
private noncomputable def sectionFiber_sheafificationComparison
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v)}
    (a : F ⟶ G) (X : BigFppfOver B S hS) (y : G.obj (Opposite.op X)) :
    sheafify (BigFppfOver.topology B S hS |>.over X)
        (sectionFiber B S hS a X y) ≅
      sectionFiber B S hS
        (sheafifyMap (BigFppfOver.topology B S hS) a) X
        ((toSheafify (BigFppfOver.topology B S hS) G).app (Opposite.op X) y) := by
  let J := BigFppfOver.topology B S hS |>.over X
  let P := sectionFiber B S hS a X y
  let Q := sectionFiber B S hS (sheafifyMap
    (BigFppfOver.topology B S hS) a) X
      ((toSheafify (BigFppfOver.topology B S hS) G).app (Opposite.op X) y)
  let θ := sectionFiber_toSheafifyMap B S hS a X y
  have hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (sheafify (BigFppfOver.topology B S hS) F) :=
    ((presheafToSheaf _ _).obj F).property
  have hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS)
      (sheafify (BigFppfOver.topology B S hS) G) :=
    ((presheafToSheaf _ _).obj G).property
  have hQ : Presheaf.IsSheaf J Q :=
    (isSheaf_iff_isSheaf_of_type J Q).2 (by
      simpa [J, Q] using sectionFiber_isSheaf B S hS (sheafifyMap
        (BigFppfOver.topology B S hS) a) X _ hF hG)
  have : ∀ R : (Over X)ᵒᵖ ⥤ Type (max (u + 1) v),
      Presheaf.IsLocallyInjective J (toSheafify J R) :=
    fun R => (toSheafify_isLocallyBijective_large J R).2
  have : ∀ R : (Over X)ᵒᵖ ⥤ Type (max (u + 1) v),
      Presheaf.IsLocallySurjective J (toSheafify J R) :=
    fun R => (toSheafify_isLocallyBijective_large J R).1
  have : J.WEqualsLocallyBijective (Type (max (u + 1) v)) :=
    GrothendieckTopology.WEqualsLocallyBijective.mk' (J := J) (A := Type (max (u + 1) v))
  have : Presheaf.IsLocallyInjective J θ :=
    sectionFiber_toSheafifyMap_locallyInjective B S hS a X y
  have : Presheaf.IsLocallySurjective J θ :=
    sectionFiber_toSheafifyMap_locallySurjective B S hS a X y
  have : IsIso ((presheafToSheaf J (Type (max (u + 1) v))).map θ) :=
    (J.W_iff θ).mp (J.W_of_isLocallyBijective θ)
  have : IsIso (sheafifyMap J θ) := by
    change IsIso ((sheafToPresheaf J (Type (max (u + 1) v))).map
      ((presheafToSheaf J (Type (max (u + 1) v))).map θ))
    infer_instance
  have : IsIso (toSheafify J Q) := isIso_toSheafify _ hQ
  exact asIso (sheafifyMap J θ) ≪≫ (asIso (toSheafify J Q)).symm

/-- The section fibre of the sheafified transformation over the image of a section is limit
preserving as soon as the section fibre of the original transformation is. -/
private theorem limitPreserving_sheafified_sectionFiber [UnivLE.{max w w', u}]
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v)}
    (a : F ⟶ G) (Y : BigFppfOver B S hS) (y : G.obj (Opposite.op Y))
    (hP : LimitPreserving.{u, max (u + 1) v, w, w', u + 1, u}
      (Over.forget Y ⋙ BigFppfOver.toScheme B S hS)
      (sectionFiber B S hS a Y y)) :
    LimitPreserving.{u, max (u + 1) v, w, w', u + 1, u}
      (Over.forget Y ⋙ BigFppfOver.toScheme B S hS)
      (sectionFiber B S hS (sheafifyMap
        (BigFppfOver.topology B S hS) a) Y
        ((toSheafify (BigFppfOver.topology B S hS) G).app (Opposite.op Y) y)) := by
  let Jbase := B.topology.over (B.obj hS)
  let J := Jbase.over Y
  let K := B.topology.over Y.left
  let e := Over.iteratedSliceEquiv Y
  let P := sectionFiber B S hS a Y y
  have hP' := limitPreserving_whiskerEquivalence e.symm rfl P hP
  have hK : K = BigFppfOver.topology B Y.left.1 Y.left.2 := by
    dsimp [K, BigFppfOver.topology, BigFppfOver]
    congr 2
  have hplus := limitPreserving_sheafify B Y.left.1 Y.left.2
      (e.inverse.op ⋙ P) hP'
  have hmath := limitPreserving_of_natIso
    (plusPlusIsoSheafify (BigFppfOver.topology B Y.left.1 Y.left.2)
      (Type (max (u + 1) v)) (e.inverse.op ⋙ P)) hplus
  have hsh : LimitPreserving.{u, max (u + 1) v, w, w', u + 1, u}
      (BigFppfOver.toScheme B Y.left.1 Y.left.2)
      (sheafify K (e.inverse.op ⋙ P)) := by
    simpa [hK] using hmath
  have hsh' := limitPreserving_whiskerEquivalence e rfl (sheafify K (e.inverse.op ⋙ P)) hsh
  exact limitPreserving_of_natIso (sectionFiber_sheafificationComparison B S hS a Y y)
    (limitPreserving_of_natIso (sheafify_equiv_iso e J K P) hsh')

/-- Limit preservation of the section fibre of the sheafified transformation, restricted to
the slice over a member of a covering on which the chosen section comes from the presheaf. -/
private theorem limitPreserving_local_sectionFiber [UnivLE.{max w w', u}]
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v)}
    (a : F ⟶ G) (X : BigFppfOver B S hS)
    (y : (sheafify (BigFppfOver.topology B S hS) G).obj (Opposite.op X))
    (Y : BigFppfOver B S hS) (f : Y ⟶ X)
    (y₀ : G.obj (Opposite.op Y))
    (hy : (sheafify (BigFppfOver.topology B S hS) G).map f.op y =
      (toSheafify (BigFppfOver.topology B S hS) G).app (Opposite.op Y) y₀)
    (hP : LimitPreserving.{u, max (u + 1) v, w, w', u + 1, u}
      (Over.forget Y ⋙ BigFppfOver.toScheme B S hS)
      (sectionFiber B S hS a Y y₀)) :
    LimitPreserving.{u, max (u + 1) v, w, w', u + 1, u}
      (Over.forget Y.left ⋙ B.inclusion)
      ((Over.map f.left).op ⋙ (Over.iteratedSliceEquiv X).inverse.op ⋙
        sectionFiber B S hS (sheafifyMap
          (BigFppfOver.topology B S hS) a) X
          y) := by
  let J := BigFppfOver.topology B S hS
  let QX := sectionFiber B S hS (sheafifyMap J a) X y
  let QY := sectionFiber B S hS (sheafifyMap J a) Y
    ((toSheafify J G).app (Opposite.op Y) y₀)
  let eX := Over.iteratedSliceEquiv X
  let eY := Over.iteratedSliceEquiv Y
  have hQY := limitPreserving_sheafified_sectionFiber B S hS a Y y₀ hP
  have hBase := sectionFiber_baseChangeIso.{u, v} B S hS (sheafifyMap J a) f
    y ((toSheafify J G).app (Opposite.op Y) y₀) hy
  have hRestr : LimitPreserving.{u, max (u + 1) v, w, w', u + 1, u}
      (Over.forget Y ⋙ BigFppfOver.toScheme B S hS)
      ((Over.map f).op ⋙ QX) :=
    limitPreserving_of_natIso hBase.symm hQY
  have hDirect := limitPreserving_whiskerEquivalence eY.symm (by rfl)
    ((Over.map f).op ⋙ QX) hRestr
  let α := Over.iteratedSliceEquivOverMapIso (f := Y) (g := X) f
  let β : eY.inverse ⋙ Over.map f ≅ Over.map f.left ⋙ eX.inverse :=
    (Functor.isoWhiskerLeft eY.inverse α.symm) ≪≫
      Functor.isoWhiskerRight eY.counitIso (Over.map f.left ⋙ eX.inverse)
  let γ : eY.inverse.op ⋙ (Over.map f).op ⋙ QX ≅
      (Over.map f.left).op ⋙ eX.inverse.op ⋙ QX :=
    NatIso.ofComponents (fun W => (QX.mapIso (β.app W.unop).op).symm) (by
      intro W W' g
      simp only [Functor.comp_obj, Functor.comp_map, Functor.mapIso_inv,
        Iso.symm_hom, Iso.op_inv]
      calc
        _ = QX.map
            ((Over.map f).op.map (eY.inverse.op.map g) ≫
              (β.app W'.unop).inv.op) := by rw [Functor.map_comp]
        _ = QX.map
            ((β.app W.unop).inv.op ≫
              (eX.inverse.op.map ((Over.map f.left).op.map g))) := by
          congr 1
        _ = _ := by rw [Functor.map_comp])
  exact limitPreserving_of_natIso γ hDirect

/-- Sheafification preserves relative limit preservation of a transformation
of presheaves on the big fppf site. -/
@[stacks 049Q]
public theorem relativelyLimitPreserving_sheafifyMap [UnivLE.{max w w', u}]
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type (max (u + 1) v)}
    (a : F ⟶ G)
    (ha : RelativelyLimitPreserving.{u, max (u + 1) v, w, w'}
      B S hS a) :
    RelativelyLimitPreserving.{u, max (u + 1) v, w, w'} B S hS
      (sheafifyMap (BigFppfOver.topology B S hS) a) := by
  intro X y
  let J := BigFppfOver.topology B S hS
  let Q := sectionFiber B S hS (sheafifyMap J a) X y
  let e := Over.iteratedSliceEquiv X
  let P := e.inverse.op ⋙ Q
  have hF : Presheaf.IsSheaf J (sheafify J F) := ((presheafToSheaf _ _).obj F).property
  have hG : Presheaf.IsSheaf J (sheafify J G) := ((presheafToSheaf _ _).obj G).property
  have hQ : Presieve.IsSheaf (J.over X) Q :=
    sectionFiber_isSheaf B S hS (sheafifyMap J a) X y hF hG
  have hP : Presieve.IsSheaf
      (BigFppfOver.topology B X.left.1 X.left.2) P := by
    have hcont : e.inverse.IsContinuous
        (BigFppfOver.topology B X.left.1 X.left.2) (J.over X) := by
      show X.iteratedSliceBackward.IsContinuous
        (B.topology.over X.left) ((B.topology.over (B.obj hS)).over X)
      infer_instance
    exact e.inverse.op_comp_isSheaf_of_isSheaf_type
      (J := BigFppfOver.topology B X.left.1 X.left.2)
      (K := J.over X) hQ
  obtain ⟨E, hE, hlocal⟩ := exists_fppf_local_sections B S hS X y
  have hlocalLP (i : E.I₀) :
      LimitPreserving.{u, max (u + 1) v, w, w', u + 1, u}
        (Over.forget (E.X i) ⋙ B.inclusion)
        ((Over.map (E.f i)).op ⋙ P) := by
    obtain ⟨Y, f, y₀, hY, hf, hy⟩ := hlocal i
    let Y' : BigFppfOver B S hS := Over.mk (E.f i ≫ X.hom)
    let f' : Y' ⟶ X := Over.homMk (E.f i)
    have hf' : f.left = eqToHom hY ≫ E.f i := by simpa using hf
    have hbase : (eqToIso hY).hom ≫ Y'.hom = Y.hom := by simp [Y', ← Over.w f, hf']
    let eY : Y ≅ Y' := Over.isoMk (eqToIso hY) hbase
    have hcomp : eY.hom ≫ f' = f := Over.OverMorphism.ext hf'.symm
    have hcomp' : eY.inv ≫ f = f' := by rw [← hcomp, Iso.inv_hom_id_assoc]
    let y' := G.map eY.inv.op y₀
    have hy' : (sheafify J G).map f'.op y =
        (toSheafify J G).app (Opposite.op Y') y' := by
      calc
        _ = (sheafify J G).map eY.inv.op
            ((sheafify J G).map f.op y) := by
          rw [← Functor.map_comp_apply, ← op_comp, hcomp']
        _ = (sheafify J G).map eY.inv.op
            ((toSheafify J G).app (Opposite.op Y) y₀) := by rw [hy]
        _ = (toSheafify J G).app (Opposite.op Y') y' := by
          simp [y']
    have hLP := limitPreserving_local_sectionFiber B S hS a X y Y' f' y' hy'
      (ha Y' y')
    simpa [P, e, Y', f'] using hLP
  exact limitPreserving_of_natIso (Functor.isoWhiskerRight e.op.unitIso.symm Q)
    (limitPreserving_whiskerEquivalence e (by rfl) P
      (limitPreserving_of_fppfCover B X.left.1 X.left.2 P
        ((isSheaf_iff_isSheaf_of_type _ _).2 hP) E hE hlocalLP))

/-- A section fibre of a transformation of fppf sheaves receiving a locally bijective map
from a limit-preserving presheaf on the slice is limit preserving. -/
public theorem limitPreserving_sectionFiber_of_isLocallyBijective
    (B : BigFppfSite.{u}) (S : Scheme.{u}) (hS : B.Contains S)
    {F G : (BigFppfOver B S hS)ᵒᵖ ⥤ Type u} (a : F ⟶ G)
    (hF : Presheaf.IsSheaf (BigFppfOver.topology B S hS) F)
    (hG : Presheaf.IsSheaf (BigFppfOver.topology B S hS) G)
    (X : BigFppfOver B S hS) (y : G.obj (Opposite.op X))
    {P : (Over X)ᵒᵖ ⥤ Type u} (η : P ⟶ sectionFiber B S hS a X y)
    [Presheaf.IsLocallySurjective ((BigFppfOver.topology B S hS).over X) η]
    [Presheaf.IsLocallyInjective ((BigFppfOver.topology B S hS).over X) η]
    (hP : LimitPreserving.{u, u, u, u, u + 1}
      (Over.forget X ⋙ BigFppfOver.toScheme B S hS) P) :
    LimitPreserving.{u, u, u, u, u + 1}
      (Over.forget X ⋙ BigFppfOver.toScheme B S hS)
      (sectionFiber B S hS a X y) := by
  let J := BigFppfOver.topology B S hS
  let Q := sectionFiber B S hS a X y
  let e := Over.iteratedSliceEquiv X
  let K := BigFppfOver.topology B X.left.1 X.left.2
  have hcont : e.inverse.IsContinuous K (J.over X) := by
    show X.iteratedSliceBackward.IsContinuous (B.topology.over X.left)
      ((B.topology.over (B.obj hS)).over X)
    infer_instance
  have hcocont : e.inverse.IsCocontinuous K (J.over X) := by
    show X.iteratedSliceBackward.IsCocontinuous (B.topology.over X.left)
      ((B.topology.over (B.obj hS)).over X)
    infer_instance
  have hQ : Presieve.IsSheaf (J.over X) Q :=
    sectionFiber_isSheaf B S hS a X y hF hG
  have hQ' : Presieve.IsSheaf K (e.inverse.op ⋙ Q) :=
    e.inverse.op_comp_isSheaf_of_isSheaf_type (J := K) (K := J.over X) hQ
  have hsurj : Presheaf.IsLocallySurjective K (Functor.whiskerLeft e.inverse.op η) :=
    Presheaf.isLocallySurjective_whisker K (J.over X) e.inverse η
  have hinj : Presheaf.IsLocallyInjective K (Functor.whiskerLeft e.inverse.op η) :=
    Presheaf.isLocallyInjective_whisker K (J.over X) e.inverse η
  have hP' := limitPreserving_whiskerEquivalence e.symm (by rfl) P hP
  have hres := limitPreserving_of_isLocallyBijective.{u, u, u, u} B X.left.1 X.left.2
    (Functor.whiskerLeft e.inverse.op η)
    ((isSheaf_iff_isSheaf_of_type _ _).2 hQ') hP'
  exact limitPreserving_of_natIso (Functor.isoWhiskerRight e.op.unitIso.symm Q)
    (limitPreserving_whiskerEquivalence e (by rfl) (e.inverse.op ⋙ Q) hres)

end AlgebraicGeometry
