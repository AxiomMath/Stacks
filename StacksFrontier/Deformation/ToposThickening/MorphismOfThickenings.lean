module

public import StacksCore.Tactic.StacksAttribute
public import StacksFrontier.Deformation.ToposThickening.Basic
public import StacksFrontier.Deformation.ToposThickening.Trivialization.RingedToposComp

/-!
# Thickenings of ringed topoi and morphisms between them

A *thickening* of ringed topoi is a morphism `i : (Sh(C), O) ⟶ (Sh(D), O')` whose underlying
geometric morphism is an equivalence and whose structure map `O' ⟶ i_*O` is locally surjective
with locally nilpotent kernel. The kernel is the *defining ideal* `I ⊂ O'` of the thickening.
A first order thickening in the sense of Stacks 08MB is a thickening, its defining ideal being
the square-zero ideal recorded by `Deformation.ToposThickening.FirstOrderThickening`.

A *morphism of thickenings* is a commutative square of morphisms of ringed topoi

```
  (Sh(C), O)  --i-->  (Sh(D), O')
      |                   |
      f                   f'
      v                   v
  (Sh(B), O_B) --t--> (Sh(B'), O_{B'})
```

whose horizontal arrows are thickenings. Writing `I = Ker(i^♯)` and `J = Ker(t^♯)`, the
structure map of `f'` carries `J` into `I` and so induces a map of `O'`-modules
`(f')^*J ⟶ I`.

## Main definitions

* `Deformation.ToposThickening.HasLocallyNilpotentKernel`: every section of the kernel of the
  structure map is locally nilpotent.
* `Deformation.ToposThickening.IsThickening`: **Stacks 08M7**, the hypothesis on the horizontal
  arrows of the square.
* `Deformation.ToposThickening.IsFirstOrderThickening`: **Stacks 08M7**, a thickening whose
  kernel ideal is square zero, as a property of a morphism.
* `Deformation.ToposThickening.IdealOfThickening`: the defining ideal of a thickening,
  presented as a submodule of the structure sheaf of the target cutting out the kernel of the
  structure map.
* `Deformation.ToposThickening.MorphismOfThickenings`: **Stacks 08M7**, the commutative
  square, with the two defining ideals.

## Main results

* `Deformation.ToposThickening.FirstOrderThickening.idealOfThickening` and
  `Deformation.ToposThickening.IsThickening.of_firstOrderThickening`: a first order thickening
  of Stacks 08MB is a thickening, with its square-zero ideal as defining ideal.
* `Deformation.ToposThickening.IsFirstOrderThickening.of_firstOrderThickening`: it is a first
  order thickening in the sense of the predicate above.
* `Deformation.ToposThickening.IdealOfThickening.fSharp_incl_apply`: the defining ideal is
  killed by the structure map.
* `Deformation.ToposThickening.IdealOfThickening.incl_injective`: two sections of the defining
  ideal with the same image in the structure sheaf are equal, so the ideal is a submodule and
  not merely a cover of the kernel.

## Implementation notes

Local nilpotence is a covering sieve on which each kernel section becomes nilpotent, which is
the sheaf form of the source's "locally nilpotent". For a first order thickening the sieve can
be taken to be the whole sieve, the square of a section of a square-zero ideal being zero
already.

The defining ideal is carried as data together with its characterizing sectionwise property,
rather than as a chosen kernel object, which is the idiom of
`Deformation.ToposThickening.FirstOrderThickening` on the same material: the structure sheaves
of the four ringed topoi have independent section universes, and a kernel taken in sheaves of
modules would need sheafification hypotheses on every one of them merely to name the ideal.
`Deformation.ToposThickening.FirstOrderThickening.idealOfThickening` shows that the data is
available whenever the source says it is.

The induced map of defining ideals `(f')^*J ⟶ I` is not part of this module: it needs the
structure map of `f'` read as a map of sheaves of modules `O_{B'} ⟶ (f')_*O'`, equivalently the
canonical comparison `(f')^*O_{B'} ⟶ O'`, which is
`AlgebraicGeometry.RingedToposHom.unitStructureMap` and
`AlgebraicGeometry.RingedToposHom.pullbackUnitStructureMap`. It is constructed in
`StacksFrontier/Deformation/ToposThickening/MorphismOfThickeningsIdealMap.lean`, together with
strictness (Stacks 08M9), so that the pullback of sheaves of modules — and with it the
sheafification hypotheses it needs on the upper two topoi — is not imposed on the square
itself.

The four ringed topoi are parameters rather than fields, so that the sheafification hypotheses
needed to form `(f')^*J` can be stated once as instance arguments.

## References

* [Stacks Project, Tag 08M7](https://stacks.math.columbia.edu/tag/08M7)
* [Stacks Project, Tag 08MB](https://stacks.math.columbia.edu/tag/08MB)
-/

@[expose] public section

open CategoryTheory CategoryTheory.Limits
open AlgebraicGeometry (RingedTopos RingedToposHom)

universe v u w v' u' w' v'' u'' w'' v''' u''' w'''

namespace Deformation.ToposThickening

section Thickening

variable {X : RingedTopos.{v, u, w}} {Y : RingedTopos.{v', u', w'}}
  [X.J.HasSheafCompose (forget RingCat.{w})] [Y.J.HasSheafCompose (forget RingCat.{w'})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [Y.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]

/-- Every local section of the kernel of the structure map of `i` becomes nilpotent on a
covering sieve. -/
def HasLocallyNilpotentKernel (i : RingedToposHom X Y) : Prop :=
  ∀ (U : Y.Cᵒᵖ) (a : Y.O.obj.obj U), i.fSharp.hom.app U a = 0 →
    ∃ R : Sieve U.unop, R ∈ Y.J U.unop ∧
      ∀ (V : Y.C) (p : V ⟶ U.unop), R p → IsNilpotent (Y.O.obj.map p.op a)

/-- **Stacks 08M7.** A thickening of ringed topoi: the underlying geometric morphism is an
equivalence of topoi, the structure map is locally surjective, and its kernel ideal is locally
nilpotent. This is the hypothesis the source places on the horizontal arrows of a morphism of
thickenings. -/
@[stacks 08M7 "the horizontal arrows are thickenings"]
def IsThickening (i : RingedToposHom X Y) : Prop :=
  i.toToposHom.pushforward.IsEquivalence ∧
    Presheaf.IsLocallySurjective Y.J i.fSharp.hom ∧ HasLocallyNilpotentKernel i

/-- **Stacks 08M7.** The defining ideal `I = Ker(i^♯) ⊂ O'` of a thickening `i`, presented as a
sheaf of `O'`-modules together with an inclusion into `O'` whose sections are exactly the
sections killed by the structure map. -/
@[stacks 08M7 "the defining ideal of a thickening"]
structure IdealOfThickening (i : RingedToposHom X Y) where
  /-- The ideal, as a sheaf of modules over the structure sheaf of the target. -/
  I : SheafOfModules.{w'} (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
  /-- Its inclusion into the structure sheaf of the target. -/
  incl : I ⟶ SheafOfModules.unit (Stacks.SheafOfModules.Tensor.ringSheaf Y.O)
  /-- The ideal is exactly the kernel of the structure map. -/
  kernel : ∀ (U : Y.Cᵒᵖ) (a : Y.O.obj.obj U),
    i.fSharp.hom.app U a = 0 ↔
      ∃ b : I.val.obj U, (show Y.O.obj.obj U from incl.val.app U b) = a
  /-- The inclusion is injective on sections, so the ideal is a submodule of `O'`. -/
  injective : ∀ U : Y.Cᵒᵖ, Function.Injective (incl.val.app U)

namespace IdealOfThickening

variable {i : RingedToposHom X Y} (hI : IdealOfThickening i)

/-- A local section of the structure sheaf of the target killed by the structure map is the
image of a section of the defining ideal. -/
lemma exists_section (U : Y.Cᵒᵖ) (a : Y.O.obj.obj U) (ha : i.fSharp.hom.app U a = 0) :
    ∃ b : hI.I.val.obj U, (show Y.O.obj.obj U from hI.incl.val.app U b) = a :=
  (hI.kernel U a).1 ha

/-- Sections of the defining ideal are killed by the structure map. -/
lemma fSharp_incl_apply (U : Y.Cᵒᵖ) (b : hI.I.val.obj U) :
    i.fSharp.hom.app U (show Y.O.obj.obj U from hI.incl.val.app U b) = 0 :=
  (hI.kernel U _).2 ⟨b, rfl⟩

/-- Two sections of the defining ideal with the same image in the structure sheaf are equal. -/
lemma incl_injective {U : Y.Cᵒᵖ} {b b' : hI.I.val.obj U}
    (h : (show Y.O.obj.obj U from hI.incl.val.app U b) =
      (show Y.O.obj.obj U from hI.incl.val.app U b')) : b = b' :=
  hI.injective U h

end IdealOfThickening

/-- The square-zero ideal of a first order thickening of Stacks 08MB, read as a sheaf of
modules over the structure sheaf of the target, is a defining ideal in the sense above. -/
noncomputable def FirstOrderThickening.idealOfThickening {i : RingedToposHom X Y}
    (h : FirstOrderThickening i) : IdealOfThickening i where
  I := (SheafOfModules.restrictScalars
    ((sheafCompose Y.J (forget₂ CommRingCat RingCat)).map i.fSharp)).obj h.I
  incl := h.incl
  kernel := h.kernel
  injective := h.injective

/-- Two local sections killed by the structure map of a first order thickening multiply to
zero. -/
private lemma mul_eq_zero_of_firstOrderThickening {i : RingedToposHom X Y}
    (h : FirstOrderThickening i) (U : Y.Cᵒᵖ) (a b : Y.O.obj.obj U)
    (ha : i.fSharp.hom.app U a = 0) (hb : i.fSharp.hom.app U b = 0) : a * b = 0 := by
  obtain ⟨α, hα⟩ := h.exists_ideal_section U a ha
  obtain ⟨β, hβ⟩ := h.exists_ideal_section U b hb
  rw [← hα, ← hβ]
  exact h.square_zero U α β

/-- A section of a square-zero ideal is nilpotent after any restriction, so the kernel of the
structure map of a first order thickening is locally nilpotent. -/
lemma HasLocallyNilpotentKernel.of_firstOrderThickening {i : RingedToposHom X Y}
    (h : FirstOrderThickening i) : HasLocallyNilpotentKernel i := by
  intro U a ha
  refine ⟨⊤, Y.J.top_mem _, fun V p _ => ⟨2, ?_⟩⟩
  rw [pow_two, ← map_mul, mul_eq_zero_of_firstOrderThickening h U a a ha ha, map_zero]

/-- **Stacks 08M7.** A first order thickening of ringed topoi in the sense of Stacks 08MB is a
thickening: its structure map is locally surjective by assumption and its square-zero kernel is
in particular locally nilpotent. -/
@[stacks 08M7 "a first order thickening is a thickening"]
theorem IsThickening.of_firstOrderThickening {i : RingedToposHom X Y}
    (h : FirstOrderThickening i) : IsThickening i :=
  ⟨h.equiv, h.surjective, HasLocallyNilpotentKernel.of_firstOrderThickening h⟩

/-- **Stacks 08M7.** A first order thickening of ringed topoi, as a property of a morphism: a
thickening whose kernel ideal is square zero. This is the predicate form of the structure
`Deformation.ToposThickening.FirstOrderThickening` of Stacks 08MB, which in addition names the
ideal. -/
@[stacks 08M7 "first order thickening, as a property"]
def IsFirstOrderThickening (i : RingedToposHom X Y) : Prop :=
  IsThickening i ∧
    ∀ (U : Y.Cᵒᵖ) (a b : Y.O.obj.obj U),
      i.fSharp.hom.app U a = 0 → i.fSharp.hom.app U b = 0 → a * b = 0

/-- A first order thickening is a thickening. -/
lemma IsFirstOrderThickening.isThickening {i : RingedToposHom X Y}
    (h : IsFirstOrderThickening i) : IsThickening i := h.1

/-- **Stacks 08M7.** A first order thickening in the sense of Stacks 08MB has the property of
being a first order thickening: its kernel is the square-zero ideal it names. -/
@[stacks 08M7 "08MB implies the property"]
theorem IsFirstOrderThickening.of_firstOrderThickening {i : RingedToposHom X Y}
    (h : FirstOrderThickening i) : IsFirstOrderThickening i := by
  exact ⟨IsThickening.of_firstOrderThickening h, mul_eq_zero_of_firstOrderThickening h⟩

end Thickening

section Square

variable (X : RingedTopos.{v, u, w}) (X' : RingedTopos.{v', u', w'})
  (S : RingedTopos.{v'', u'', w''}) (S' : RingedTopos.{v''', u''', w'''})
  [X.J.HasSheafCompose (forget RingCat.{w})] [X'.J.HasSheafCompose (forget RingCat.{w'})]
  [S.J.HasSheafCompose (forget RingCat.{w''})] [S'.J.HasSheafCompose (forget RingCat.{w'''})]
  [X.J.HasSheafCompose (forget₂ CommRingCat.{w} RingCat.{w})]
  [X'.J.HasSheafCompose (forget₂ CommRingCat.{w'} RingCat.{w'})]
  [S.J.HasSheafCompose (forget₂ CommRingCat.{w''} RingCat.{w''})]
  [S'.J.HasSheafCompose (forget₂ CommRingCat.{w'''} RingCat.{w'''})]

/-- **Stacks 08M7.** A morphism of thickenings of ringed topoi: a commutative square of
morphisms of ringed topoi whose horizontal arrows `i` and `t` are thickenings, together with
their defining ideals `I = Ker(i^♯) ⊂ O'` and `J = Ker(t^♯) ⊂ O_{B'}`. -/
@[stacks 08M7 "the commutative square"]
structure MorphismOfThickenings where
  /-- The upper horizontal arrow, a thickening. -/
  i : RingedToposHom X X'
  /-- The lower horizontal arrow, a thickening. -/
  t : RingedToposHom S S'
  /-- The left vertical arrow. -/
  f : RingedToposHom X S
  /-- The right vertical arrow. -/
  f' : RingedToposHom X' S'
  /-- The upper arrow is a thickening. -/
  i_isThickening : IsThickening i
  /-- The lower arrow is a thickening. -/
  t_isThickening : IsThickening t
  /-- The square commutes. -/
  comm : f'.comp i = t.comp f
  /-- The defining ideal `I = Ker(i^♯)` of the upper thickening. -/
  idealI : IdealOfThickening i
  /-- The defining ideal `J = Ker(t^♯)` of the lower thickening. -/
  idealJ : IdealOfThickening t

namespace MorphismOfThickenings

variable {X X' S S'}

/-- The square of a morphism of thickenings commutes on underlying morphisms of topoi. -/
lemma comm_toToposHom (D : MorphismOfThickenings X X' S S') :
    D.f'.toToposHom.comp D.i.toToposHom = D.t.toToposHom.comp D.f.toToposHom :=
  congrArg AlgebraicGeometry.RingedToposHom.toToposHom D.comm

end MorphismOfThickenings

end Square

end Deformation.ToposThickening

end
